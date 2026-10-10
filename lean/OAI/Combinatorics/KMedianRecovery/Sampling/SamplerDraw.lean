import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.ActionMachine
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplerWeights
import OAI.Combinatorics.KMedianRecovery.Recovery.DyadicLookup

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Draw
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
def pack (cfg : List Bool) (s : Option (RationalSampling.State n)) (b : ℕ) (tape : List Bool) : List Bool :=
  encode [cfg,BinarySamplingState.optionBits s,List.replicate b true,tape]
noncomputable def input (x : List Bool) : List Bool := pairBits (field 0 x,field 1 x)
noncomputable def input_computes : PolyComputes input := (field_computes 0).pair (field_computes 1)
noncomputable def actions (x : List Bool) : List Bool := BinaryActions.run (pairBits (c 2 (input x),c 9 (input x)))
noncomputable def actions_computes : PolyComputes actions := by
  have computation := ((input_computes.comp (c_computes 2)).pair (input_computes.comp (c_computes 9))).comp BinaryActions.run_computes
  unfold actions
  simpa only [Function.comp_def] using computation
noncomputable def weights (x : List Bool) : List Bool := mapWith (fun y=>BinaryRational.encode (Weights.weight y))
  (pairBits (Weights.context (input x),actions x))
noncomputable def weights_computes : PolyComputes weights := by
  have computation := ((input_computes.comp Weights.context_computes).pair actions_computes).comp (mapWith_computes Weights.weight_computes)
  unfold weights
  simpa only [Function.comp_def] using computation
noncomputable def index (x : List Bool) : List Bool := BinaryDyadic.run (encode [field 2 x,weights x,(0:ℕ).bits,field 3 x])
noncomputable def index_computes : PolyComputes index :=
  (cons_computes (field_computes 2) (cons_computes weights_computes
    (cons_computes (const_computes _) (cons_computes (field_computes 3) (const_computes []))))).comp BinaryDyadic.run_computes
noncomputable def run (x : List Bool) : List Bool := Lookup.run (pairBits (index x,actions x))
noncomputable def run_computes : PolyComputes run := (index_computes.pair actions_computes).comp Lookup.run_computes
lemma input_pack (cfg : List Bool) (s : Option (RationalSampling.State n)) (b : ℕ) (tape : List Bool) :
    input (pack cfg s b tape)=pairBits (cfg,BinarySamplingState.optionBits s) := by
  simp only [input,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma actions_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (RationalSampling.State n)) (b : ℕ) (tape : List Bool) :
    actions (pack (config δ D F S Δ P κ m M E J) s b tape)=
      encode ((RationalSampling.actions D M E J).map (RationalSampling.actionCode D M E J)) := by
  simp only [actions,input_pack,c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryActions.run_pair]
lemma weights_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (RationalSampling.State n)) (b : ℕ) (tape : List Bool) :
    weights (pack (config δ D F S Δ P κ m M E J) s b tape)=
      RationalArray.encode ((RationalSampling.actions D M E J).map (RationalSampling.transitionWeight δ D S Δ M E J s)) := by
  simp only [weights,input_pack,actions_pack,mapWith_encode,List.map_map,Function.comp_def,Weights.weight_pair,RationalArray.encode]
lemma run_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (RationalSampling.State n)) (b : ℕ) (seed : Fin b→Bool) :
    run (pack (config δ D F S Δ P κ m M E J) s b (List.ofFn seed))=
      RationalSampling.actionCode D M E J (Dyadic.Canonical.draw
        (fun a=>(RationalSampling.transitionWeight δ D S Δ M E J s a:ℝ)) b (Sum.inl ()) (RationalSampling.actions D M E J) seed) := by
  rw [run,index,weights_pack,actions_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact BinaryDyadic.lookup_draw _ _ _ _ rfl b seed
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

namespace MetricKMedianRecovery.RationalSampling
open BitMachine RationalHeight
variable {n : ℕ}
lemma height_max {q r : ℚ} {H : ℕ} (hq : Height q H) (hr : Height r H) : Height (max q r) H := by
  rcases le_total q r with h|h
  · simpa only [max_eq_right h] using hr
  · simpa only [max_eq_left h] using hq
lemma height_minimum (qs : List ℚ) (H : ℕ) (hh : ∀ q∈qs,Height q H) : Height (RationalMin.minimum qs) H := by
  have hf (xs : List ℚ) (a : ℚ) (ha : Height a H) (hx : ∀ q∈xs,Height q H) : Height (xs.foldl min a) H := by
    induction xs generalizing a with
    | nil=>exact ha
    | cons q xs ih=>
      exact ih _ (ha.min (hx q (by simp))) (fun r hr=>hx r (by simp only [List.mem_cons];exact Or.inr hr))
  apply hf _ _ _ hh
  cases qs with
  | nil=>exact RationalHeight.zero H
  | cons q qs=>exact hh q (by simp)
def State.Height (s : State n) (H : ℕ) : Prop := ∀ z∈s.leaves,RationalHeight.Height z.2 H
lemma State.Height.mono {s : State n} {H K : ℕ} (hs : s.Height H) (hHK : H≤K) : s.Height K :=
  fun z hz=>(hs z hz).mono hHK
lemma height_nat (x H : ℕ) (hx : x≤H) : Height (x:ℚ) H :=
  RationalHeight.natCast x H (hx.trans (Nat.le_of_lt (Nat.lt_two_pow_self (n:=H))))
lemma population_height (δ : Fin n→Fin n→ℚ) (D : Finset (Fin n)) (P : ℚ) (m H : ℕ)
    (hd : ∀ i j,Height (δ i j) H) (hP : Height P H) (hn : n≤H) (hm : m≤H) (w : Fin n) :
    Height (BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w)) (3*H) := by
  apply height_minimum
  intro q hq
  obtain ⟨d,hdmem,rfl⟩:=List.mem_map.mp hq
  apply height_max
  · obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hdmem
    exact (hd w z).mono (by omega)
  · apply (hP.div ((height_nat m H hm).mul (height_nat _ H ?_))).mono (by omega)
    have hl : (BinaryPopulation.distanceList δ D w).length=D.card := by
      simp only [BinaryPopulation.distanceList,List.length_map,Finset.length_sort]
    exact (List.length_filter_le _ _).trans (hl.le.trans ((Finset.card_le_univ D).trans (by simpa using hn)))
lemma nearest_height (δ : Fin n→Fin n→ℚ) (s : State n) (w : Fin n) (H K : ℕ)
    (hd : ∀ i j,Height (δ i j) H) (hs : s.Height K) (r : ℚ) (hr : nearestLeaf δ s w=some r) :
    Height r (H+K+1) := by
  unfold nearestLeaf at hr
  split_ifs at hr with he
  cases Option.some.inj hr
  apply height_minimum
  intro q hq
  obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hq
  exact (hd w z.1).add (hs z hz)
def heightIncrement (H : ℕ) : ℕ := 10*(H+1)^2
lemma menu_height (δ : Fin n→Fin n→ℚ) (D : Finset (Fin n)) (P κ : ℚ) (m M E J H K : ℕ)
    (hd : ∀ i j,Height (δ i j) H) (hP : Height P H) (hκ : Height κ H)
    (hn : n≤H) (hm : m≤H) (hM : M≤H) (hE : E≤H) (hJ : J≤H)
    (s : State n) (hs : s.Height K) (w : Fin n) (e : Sampling.Entry M E J) (R : ℚ)
    (hr : menuRadius δ D P κ m M E J s w e=some R) : Height R (K+heightIncrement H) := by
  rcases e with j | (e | j)
  · cases Option.some.inj hr
    rw [←Nat.cast_succ]
    apply (((height_nat (j.val+1) H (by omega)).mul hκ).mul (population_height δ D P m H hd hP hn hm w)).mono
    dsimp [heightIncrement];nlinarith
  · simp only [menuRadius] at hr
    obtain ⟨r,hr0,he⟩:=Option.map_eq_some_iff.mp hr
    rw [←he]
    have h1 : Height (1:ℚ) 1 := by norm_num [RationalHeight.Height]
    have hh := (nearest_height δ s w H K hd hs r hr0).div ((h1.add hκ).pow e.val)
    apply hh.mono
    have he : e.val≤H := le_trans (Nat.le_of_lt_succ e.isLt) hE
    have hp := Nat.mul_le_mul_right (1+H+1) he
    dsimp [heightIncrement];nlinarith
  · cases Option.some.inj hr
    rw [←Nat.cast_succ]
    apply (((height_nat (j.val+1) H (by omega)).mul hκ).mul (population_height δ D P m H hd hP hn hm w)).mono
    dsimp [heightIncrement];nlinarith
lemma retain_height (m : ℕ) (s t : State n) (K : ℕ) (hs : s.Height K) (ht : retain m s=some t) : t.Height K := by
  unfold retain at ht
  split_ifs at ht
  cases Option.some.inj ht
  exact hs
lemma update_height (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J H K : ℕ)
    (hd : ∀ i j,Height (δ i j) H) (hP : Height P H) (hκ : Height κ H)
    (hn : n≤H) (hm : m≤H) (hM : M≤H) (hE : E≤H) (hJ : J≤H)
    (s t : State n) (hs : s.Height K) (a : Sampling.Action D M E J)
    (ht : update δ D F S Δ P κ m M E J (some s) a=some t) : t.Height (K+heightIncrement H) := by
  simp only [update] at ht
  split_ifs at ht
  rcases a with u | (w | ⟨w,e⟩)
  · contradiction
  · dsimp only at ht
    split_ifs at ht
    apply retain_height m _ t _ _ ht
    exact fun z hz=>(hs z hz).mono (by omega)
  · dsimp only at ht
    cases he : menuRadius δ D P κ m M E J s w e with
    | none=>simp only [he] at ht;contradiction
    | some R=>
      simp only [he] at ht
      split_ifs at ht
      apply retain_height m _ t _ _ ht
      intro z hz
      simp only [State.add,List.mem_append,List.mem_singleton] at hz
      rcases hz with hz|rfl
      · exact (hs z hz).mono (by omega)
      · exact menu_height δ D P κ m M E J H K hd hP hκ hn hm hM hE hJ s hs w e R he
end MetricKMedianRecovery.RationalSampling

end OAI
