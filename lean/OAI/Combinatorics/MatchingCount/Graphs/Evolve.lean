import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreePairProposal
import OAI.Combinatorics.MatchingCount.Graphs.PushedFlow

namespace OAI

namespace MatchingFPRAS.FiniteChain

open Finset MatchingFPRAS.Replica

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

noncomputable def evolve (π : Ω → ℝ) (C : Ω → Ω → ℝ) : ℕ → (Ω → ℝ) → (Ω → ℝ)
  | 0, f => f
  | n+1, f => stepDensity π C (evolve π C n f)

omit [DecidableEq Ω] in
lemma evolve_mean (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hrow : ∀ a, ∑ b, C a b = π a) (n : ℕ) (f : Ω → ℝ) :
    massMean π (evolve π C n f) = massMean π f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [evolve,stepDensity_mean π hp C hrow,ih]

omit [DecidableEq Ω] in
lemma evolve_center (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hcol : ∀ b, ∑ a, C a b = π b) (n : ℕ) (f : Ω → ℝ) :
    evolve π C n (fun a => f a-1) = fun a => evolve π C n f a-1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [evolve,ih]
    have he : (fun a => evolve π C n f a-1) = fun a => 1*evolve π C n f a+(-1)*(1:ℝ) := by funext a; ring
    rw [he,stepDensity_linear,stepDensity_one π hp C hcol]
    funext a; ring

lemma lazy_decay (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (hrow : ∀ a, ∑ b, C a b = π a)
    (hcol : ∀ b, ∑ a, C a b = π b) (hlazy : ∀ a, π a/2 ≤ C a a)
    (γ : ℝ) (hγ : γ ≤ 1)
    (hgap : ∀ f, massMean π f = 0 → γ*sqNorm π f ≤ localEnergy C f)
    (f : Ω → ℝ) (hf : massMean π f = 0) (n : ℕ) :
    sqNorm π (evolve π C n f) ≤ (1-γ)^n*sqNorm π f := by
  induction n with
  | zero => simp [evolve]
  | succ n ih =>
    have hm : massMean π (evolve π C n f) = 0 := (evolve_mean π hp C hrow n f).trans hf
    have hl := lazy_l2 π hp C hC hrow hcol hlazy (evolve π C n f)
    have hg := hgap (evolve π C n f) hm
    have hh := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hγ)
    rw [evolve,pow_succ]
    nlinarith

noncomputable def deltaDensity (π : Ω → ℝ) (z a : Ω) : ℝ := if a=z then (π z)⁻¹ else 0

lemma deltaDensity_mean (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (z : Ω) :
    massMean π (deltaDensity π z) = 1 := by
  simp [massMean,deltaDensity,mul_ite,ne_of_gt (hp z)]

omit [DecidableEq Ω] in
lemma sqNorm_center (π f : Ω → ℝ) (hs : ∑ a, π a = 1) :
    sqNorm π (fun a => f a-1) = sqNorm π f-2*massMean π f+1 := by
  have he (a : Ω) : π a*(f a-1)^2 = π a*(f a)^2-2*(π a*f a)+π a := by ring
  simp only [sqNorm,massMean,he,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,hs]

lemma deltaDensity_sqNorm (π : Ω → ℝ) (_hp : ∀ a, 0 < π a) (z : Ω) :
    sqNorm π (deltaDensity π z) = (π z)⁻¹ := by
  simp only [sqNorm,deltaDensity,ite_pow,zero_pow (by decide : (2:ℕ) ≠ 0),mul_ite,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  field_simp

lemma deltaDensity_center_norm (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (hs : ∑ a, π a = 1) (z : Ω) :
    sqNorm π (fun a => deltaDensity π z a-1) = (π z)⁻¹-1 := by
  rw [sqNorm_center π _ hs,deltaDensity_sqNorm π hp,deltaDensity_mean π hp]
  ring

omit [DecidableEq Ω] in
lemma abs_sum_sq_le (π f : Ω → ℝ) (hp : ∀ a, 0 ≤ π a) (hs : ∑ a, π a = 1) :
    (∑ a, |π a*f a|)^2 ≤ sqNorm π f := by
  have hh := square_average π hp hs (fun a => |f a|)
  simpa only [abs_mul,abs_of_nonneg (hp _),sq_abs,sqNorm] using hh

noncomputable def kernel (π : Ω → ℝ) (C : Ω → Ω → ℝ) (a b : Ω) : ℝ := C a b/π a

noncomputable def walk (π : Ω → ℝ) (C : Ω → Ω → ℝ) (z : Ω) : ℕ → Ω → ℝ
  | 0, a => if a=z then 1 else 0
  | n+1, b => ∑ a, walk π C z n a*kernel π C a b

lemma walk_density (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ) (z : Ω) (n : ℕ) (a : Ω) :
    walk π C z n a = π a*evolve π C n (deltaDensity π z) a := by
  induction n generalizing a with
  | zero =>
    by_cases h : a=z
    · subst a; simp [walk,evolve,deltaDensity,ne_of_gt (hp z)]
    · simp [walk,evolve,deltaDensity,h]
  | succ n ih =>
    simp only [walk,ih,kernel,evolve,stepDensity,mul_div_cancel₀ _ (ne_of_gt (hp a))]
    apply Finset.sum_congr rfl
    intro b _
    field_simp [ne_of_gt (hp b)]

lemma meeting_bound (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (hs : ∑ a, π a = 1)
    (C : Ω → Ω → ℝ) (hC : ∀ a b, 0 ≤ C a b)
    (hrow : ∀ a, ∑ b, C a b = π a) (hcol : ∀ b, ∑ a, C a b = π b)
    (hlazy : ∀ a, π a/2 ≤ C a a) (γ : ℝ) (hγ : γ ≤ 1)
    (hgap : ∀ f, massMean π f = 0 → γ*sqNorm π f ≤ localEnergy C f)
    (z : Ω) (n : ℕ) :
    (∑ a, |walk π C z n a-π a|)^2 ≤ (1-γ)^n*((π z)⁻¹-1) := by
  let f : Ω → ℝ := fun a => deltaDensity π z a-1
  have hf : massMean π f = 0 := by
    simp only [f,massMean,mul_sub,mul_one,Finset.sum_sub_distrib,hs]
    change massMean π (deltaDensity π z)-1=0
    rw [deltaDensity_mean π hp]; ring
  have hb := lazy_decay π hp C hC hrow hcol hlazy γ hγ hgap f hf n
  have ha := abs_sum_sq_le π (evolve π C n f) (fun a => (hp a).le) hs
  have he : (fun a => π a*evolve π C n f a) = fun a => walk π C z n a-π a := by
    funext a
    dsimp only [f]
    rw [evolve_center π hp C hcol,walk_density π hp C z n]
    ring
  have hh : (∑ a, |π a*evolve π C n f a|) = ∑ a, |walk π C z n a-π a| := by
    exact congrArg (fun g : Ω → ℝ => ∑ a, |g a|) he
  rw [hh] at ha
  have hn : sqNorm π f = (π z)⁻¹-1 := deltaDensity_center_norm π hp hs z
  rw [hn] at hb
  exact ha.trans hb

end MatchingFPRAS.FiniteChain

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _

noncomputable def ladderLaw (w : BagEdge bags → ℝ) (T q : ℕ) :
    (Slot T q → PM (BagEdge.Incident (bags := bags))) → ℝ := density (slotLaw w)

noncomputable def ladderFlow
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) (w : BagEdge bags → ℝ) (T q : ℕ) :
    (Slot T q → PM (BagEdge.Incident (bags := bags))) →
      (Slot T q → PM (BagEdge.Incident (bags := bags))) → ℝ :=
  scanFlow (slotLaw w) guides (base T q) (treeLadderCapacity hbags hG w)

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : J → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℕ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG

theorem concrete_ladder_mixing (hN : 2 ≤ Fintype.card V)
    (M₀ : PM (BagEdge.Incident (bags := bags))) (T : ℕ)
    (z : Slot T (32*(10^4*Fintype.card V*D)^100) → PM (BagEdge.Incident (bags := bags)))
    (n : ℕ) :
    let q := 32*(10^4*Fintype.card V*D)^100
    let ν := ladderLaw w T q
    let C := ladderFlow hbags hG w T q
    (∑ s, |MatchingFPRAS.FiniteChain.walk ν C z n s-ν s|)^2 ≤
      (1-3/((8*(T*q^2+q):ℕ):ℝ))^n*((ν z)⁻¹-1) := by
  classical
  dsimp only
  let q : ℕ := 32*(10^4*Fintype.card V*D)^100
  let ν := ladderLaw w T q
  let C := ladderFlow hbags hG w T q
  have hq : 0 < q := by
    have hV : 0 < Fintype.card V := lt_of_lt_of_le (by norm_num) hN
    have hd : 0 < D := lt_of_lt_of_le (by norm_num) hD
    dsimp [q]; positivity
  have hM : 0 < ((8*(T*q^2+q):ℕ):ℝ) := by exact_mod_cast (by omega : 0 < 8*(T*q^2+q))
  have hp (s) : 0 < ν s := by
    apply Finset.prod_pos; intro i _; exact slotLaw_pos w i (s i)
  have hs : (∑ s, ν s) = 1 := density_sum (slotLaw w) (fun i => slotLaw_sum w i M₀)
  have hbase : (base T q).Nonempty := Finset.card_pos.mp (by rw [base_card]; exact hq)
  have hC (s t) : 0 ≤ C s t := scanFlow_nonneg (slotLaw w) (fun i a => (slotLaw_pos w i a).le)
    guides (base T q) (treeLadderCapacity hbags hG w) s t
  have hrow (s) : (∑ t, C s t) = ν s := scanFlow_row (slotLaw w) (fun i => slotLaw_sum w i M₀)
    guides (base T q) hbase (treeLadderCapacity hbags hG w) s
  have hcol (t) : (∑ s, C s t) = ν t := scanFlow_col (slotLaw w) (fun i => slotLaw_sum w i M₀)
    guides (base T q) hbase (treeLadderCapacity hbags hG w) t
  have hlazy (s) : ν s/2 ≤ C s s := scanFlow_lazy (slotLaw w) (fun i a => (slotLaw_pos w i a).le)
    guides (base T q) (treeLadderCapacity hbags hG w) s
  have hγ : 3/((8*(T*q^2+q):ℕ):ℝ) ≤ 1 := by
    apply (div_le_one hM).mpr
    exact_mod_cast (by omega : 3 ≤ 8*(T*q^2+q))
  have hgap (f) (hf : MatchingFPRAS.FiniteChain.massMean ν f = 0) :
      (3/((8*(T*q^2+q):ℕ):ℝ))*MatchingFPRAS.FiniteChain.sqNorm ν f ≤ localEnergy C f := by
    have hh := concrete_ladder_poincare (hbags := hbags) (hG := hG) height hheight hstep D hD w hw hN M₀ T f
    dsimp only at hh
    have hv : MatchingFPRAS.Replica.variance (slotLaw w) f = MatchingFPRAS.FiniteChain.sqNorm ν f := by
      have hm : MatchingFPRAS.Replica.mean (slotLaw w) f = 0 := hf
      unfold MatchingFPRAS.Replica.variance MatchingFPRAS.Replica.dot
      simp only [hm,Pi.sub_apply,sub_zero]
      unfold MatchingFPRAS.FiniteChain.sqNorm
      apply Finset.sum_congr rfl
      intro s _; change ν s*f s*f s=ν s*(f s)^2; ring
    rw [hv] at hh
    have he : localEnergy C f = scanEnergy (slotLaw w) guides (base T q) (treeLadderCapacity hbags hG w) f :=
      scanFlow_energy (slotLaw w) (fun i => slotLaw_sum w i M₀) guides (base T q) (treeLadderCapacity hbags hG w) f
    rw [← he] at hh
    change MatchingFPRAS.FiniteChain.sqNorm ν f ≤ ((8*(T*q^2+q):ℕ):ℝ)/3*localEnergy C f at hh
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hM).mpr
    linarith

  exact MatchingFPRAS.FiniteChain.meeting_bound ν hp hs C hC hrow hcol hlazy
    (3/((8*(T*q^2+q):ℕ):ℝ)) hγ hgap z n

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable def chosenEdge (A : PM inc) (v : V) : E :=
  Classical.choose (A.property.2 v (mem_univ v))

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma chosenEdge_mem (A : PM inc) (v : V) : chosenEdge A v ∈ A.val :=
  (Classical.choose_spec (A.property.2 v (mem_univ v))).1.1

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma chosenEdge_incident (A : PM inc) (v : V) : inc (chosenEdge A v) v :=
  (Classical.choose_spec (A.property.2 v (mem_univ v))).1.2

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma chosenEdge_injective (hinc : ∀ e, ∃ v, inc e v) :
    Function.Injective (chosenEdge (inc := inc)) := by
  intro A B h
  apply Subtype.ext; ext e
  have hh (A B : PM inc) (h : chosenEdge A = chosenEdge B) : e ∈ A.val → e ∈ B.val := by
    intro he
    obtain ⟨v,hv⟩ := hinc e
    have heq : e = chosenEdge A v := A.property.unique (mem_univ v) he hv
      (chosenEdge_mem A v) (chosenEdge_incident A v)
    rw [heq,congrFun h v]
    exact chosenEdge_mem B v
  exact ⟨hh A B h,hh B A h.symm⟩

omit [DecidableEq E] in
lemma pm_card_le (hinc : ∀ e, ∃ v, inc e v) :
    Fintype.card (PM inc) ≤ Fintype.card E ^ Fintype.card V := by
  classical
  simpa only [Fintype.card_fun] using Fintype.card_le_of_injective chosenEdge (chosenEdge_injective hinc)

omit [DecidableEq V] [DecidableEq E] in
lemma gibbs_mass_lower (hinc : ∀ e, ∃ v, inc e v) (w : E → ℝ)
    (D B : ℝ) (hD : 1 ≤ D) (hB : 1 ≤ B)
    (hw : ∀ e, D⁻¹ ≤ w e ∧ w e ≤ B) (A : PM inc) :
    (Fintype.card (PM inc)*(D*B)^Fintype.card V)⁻¹ ≤ gibbs w A := by
  classical
  have hD0 : 0 < D := by linarith
  have hB0 : 0 < B := by linarith
  have hw0 : ∀ e, 0 < w e := fun e => (inv_pos.mpr hD0).trans_le (hw e).1
  have lower (M : PM inc) : (D^Fintype.card V)⁻¹ ≤ matchingWeight w M := by
    have hh : (D⁻¹)^M.val.card ≤ matchingWeight w M := by
      simpa only [matchingWeight,Finset.prod_const] using Finset.prod_le_prod₀
        (fun e (_ : e ∈ M.val) => (inv_pos.mpr hD0).le) (fun e _ => (hw e).1)
    rw [inv_pow] at hh
    exact (inv_anti₀ (pow_pos hD0 _) (pow_le_pow_right₀ hD (PM.card_le_vertices hinc M))).trans hh
  have upper (M : PM inc) : matchingWeight w M ≤ B^Fintype.card V := by
    have hh : matchingWeight w M ≤ B^M.val.card := by
      simpa only [matchingWeight,Finset.prod_const] using Finset.prod_le_prod₀
        (fun e (_ : e ∈ M.val) => (hw0 e).le) (fun e _ => (hw e).2)
    exact hh.trans (pow_le_pow_right₀ hB (PM.card_le_vertices hinc M))
  have hc : 0 < (Fintype.card (PM inc):ℝ) := by
    have : Nonempty (PM inc) := ⟨A⟩
    exact_mod_cast Fintype.card_pos
  have hz : partition (inc := inc) w ≤ Fintype.card (PM inc)*B^Fintype.card V := by
    have he : partition (inc := inc) w = ∑ M : PM inc, matchingWeight w M := by
      unfold partition
      congr
      exact Subsingleton.elim _ _
    rw [he]
    calc
      _ ≤ ∑ _M : PM inc, B^Fintype.card V := Finset.sum_le_sum (fun M _ => upper M)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hp := partition_pos w hw0 A
  have hden : 0 < (Fintype.card (PM inc):ℝ)*B^Fintype.card V := mul_pos hc (pow_pos hB0 _)
  calc
    _ = (D^Fintype.card V)⁻¹/(Fintype.card (PM inc)*B^Fintype.card V) := by
      rw [mul_pow]; field_simp
    _ ≤ matchingWeight w A/partition (inc := inc) w :=
      div_le_div₀ (matchingWeight_pos w hw0 A).le (lower A) hp hz
    _ = _ := rfl

end

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

lemma tierClamp_range {c lo hi w : ℝ} (hc : 1 ≤ c) (hlo : lo ≤ 1) (hhi : 1 ≤ hi)
    (hw : lo ≤ w ∧ w ≤ hi) (t : ℕ) : lo ≤ tierClamp c t w ∧ tierClamp c t w ≤ hi := by
  have hp : 1 ≤ c^t := one_le_pow₀ hc
  have hip : (c^t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
  constructor
  · exact le_trans (le_min (hlo.trans hp) hw.1) (le_max_right _ _)
  · exact max_le (hip.trans hhi) ((min_le_right _ _).trans hw.2)

omit [DecidableEq V] [Fintype J] [DecidableEq J] in
lemma slotWeight_range (D K : ℕ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)
    (hw : ∀ e, (D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K) {T q : ℕ} (x : Slot T q) (e : BagEdge bags) :
    (D:ℝ)⁻¹ ≤ slotWeight w x e ∧ slotWeight w x e ≤ 3*4^K := by
  apply tierClamp_range
  · unfold tierBase; exact le_add_of_nonneg_right (by positivity)
  · apply inv_le_one_of_one_le₀; exact_mod_cast hD
  · have h : (1:ℝ) ≤ 4^K := one_le_pow₀ (by norm_num)
    linarith
  · exact hw e

omit [DecidableEq J] in
lemma bag_pm_card_le
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) :
    Fintype.card (PM (BagEdge.Incident (bags := bags))) ≤ (2*Fintype.card V^2)^Fintype.card V := by
  apply (pm_card_le BagEdge.exists_incident).trans
  exact Nat.pow_le_pow_left (bag_edges_card_le hbags hG) _

lemma denominator_power_bound (N D K : ℕ) (hN : 2 ≤ N) (hD : 1 ≤ D) :
    ((2*(N:ℝ)^2)^N)*((D:ℝ)*(3*4^K))^N ≤
      (2:ℝ)^(10*N*(K+Nat.clog 2 (N*D+2)+1)) := by
  let a := Nat.clog 2 (N*D+2)
  have hp : (N*D+2:ℝ) ≤ (2:ℝ)^a := by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (N*D+2)
  have hn : (N:ℝ) ≤ 2^a := by
    have hd : (1:ℝ) ≤ D := by exact_mod_cast hD
    have hn0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
    have hnd : (N:ℝ) ≤ N*D := by nlinarith
    exact hnd.trans (le_trans (by linarith) hp)
  have hd : (D:ℝ) ≤ 2^a := by
    have hn2 : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hd0 : (0:ℝ) ≤ D := Nat.cast_nonneg D
    have hnd : (D:ℝ) ≤ N*D := by nlinarith
    exact hnd.trans (le_trans (by linarith) hp)
  have hfour : (4:ℝ)^K = 2^(2*K) := by rw [pow_mul]; norm_num
  have hb : 2*(N:ℝ)^2*((D:ℝ)*(3*4^K)) ≤ 2^(3+3*a+2*K) := by
    calc
      _ ≤ 2*(2^a)^2*((2^a)*(3*4^K)) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg N) hn 2) (by norm_num))
        (mul_le_mul_of_nonneg_right hd (by positivity)) (by positivity) (by positivity)
      _ ≤ 2*(2^a)^2*((2^a)*(4*4^K)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right (by norm_num : (3:ℝ) ≤ 4) (by positivity)
      _ = _ := by
        rw [hfour]
        calc
          _ = (2:ℝ)^3*2^(a*2)*2^a*2^(2*K) := by rw [pow_mul]; norm_num; ring
          _ = _ := by simp only [← pow_add]; congr 1; omega
  calc
    _ = (2*(N:ℝ)^2*((D:ℝ)*(3*4^K)))^N := (mul_pow _ _ _).symm
    _ ≤ (2^(3+3*a+2*K))^N := pow_le_pow_left₀ (by positivity) hb N
    _ = (2:ℝ)^((3+3*a+2*K)*N) := (pow_mul _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by dsimp only [a]; nlinarith)

end

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

omit [DecidableEq J] in
lemma slotLaw_minimum_mass
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) (D K : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ Fintype.card V)
    (w : BagEdge bags → ℝ) (hw : ∀ e, (D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K)
    {T q : ℕ} (x : Slot T q) (A : PM (BagEdge.Incident (bags := bags))) :
    ((2:ℝ)^(10*Fintype.card V*(K+Nat.clog 2 (Fintype.card V*D+2)+1)))⁻¹ ≤ slotLaw w x A := by
  have hl := gibbs_mass_lower BagEdge.exists_incident (slotWeight w x) D (3*4^K)
    (by exact_mod_cast hD) (by
      have hh : (1:ℝ) ≤ 4^K := one_le_pow₀ (by norm_num)
      linarith)
    (slotWeight_range D K hD w hw x) A
  have hc : (Fintype.card (PM (BagEdge.Incident (bags := bags))):ℝ) ≤
      (2*Fintype.card V^2:ℝ)^Fintype.card V := by exact_mod_cast bag_pm_card_le hbags hG
  have hd := (mul_le_mul_of_nonneg_right hc (by positivity : (0:ℝ) ≤ ((D:ℝ)*(3*4^K))^Fintype.card V)).trans
    (denominator_power_bound (Fintype.card V) D K hN hD)
  have hp : 0 < (Fintype.card (PM (BagEdge.Incident (bags := bags))):ℝ)*
      ((D:ℝ)*(3*4^K))^Fintype.card V := by
    have : Nonempty (PM (BagEdge.Incident (bags := bags))) := ⟨A⟩
    have hc0 : (0:ℝ) < Fintype.card (PM (BagEdge.Incident (bags := bags))) := by exact_mod_cast Fintype.card_pos
    have hd0 : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    positivity
  exact (inv_anti₀ hp hd).trans hl

omit [DecidableEq J] in
lemma ladderLaw_power_lower
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) (D K : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ Fintype.card V)
    (w : BagEdge bags → ℝ) (hw : ∀ e, (D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K) (T q : ℕ)
    (z : Slot T q → PM (BagEdge.Incident (bags := bags))) :
    ((2:ℝ)^(10*Fintype.card V*q*(T+1)*(K+Nat.clog 2 (Fintype.card V*D+2)+1)))⁻¹ ≤ ladderLaw w T q z := by
  have hh := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun (x : Slot T q) _ => (by positivity : (0:ℝ) ≤ ((2:ℝ)^(10*Fintype.card V*(K+Nat.clog 2 (Fintype.card V*D+2)+1)))⁻¹))
    (fun x _ => slotLaw_minimum_mass hbags hG D K hD hN w hw x (z x))
  simp only [prod_const,card_univ,slots_card,← inv_pow,← pow_mul] at hh
  have he : 10*Fintype.card V*(K+Nat.clog 2 (Fintype.card V*D+2)+1)*((T+1)*q) =
      10*Fintype.card V*q*(T+1)*(K+Nat.clog 2 (Fintype.card V*D+2)+1) := by ring
  rw [he] at hh
  simpa only [inv_pow,ladderLaw,density] using hh

end MatchingFPRAS.Transport

end OAI
