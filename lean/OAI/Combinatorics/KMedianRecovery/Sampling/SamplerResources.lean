import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelSize
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplingPotential

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic RationalHeight
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
def runPack (cfg : List Bool) (m b : ℕ) (seeds : List (Fin b→Bool)) : List Bool :=
  encode [cfg,List.replicate m true,List.replicate b true,encode (seeds.map List.ofFn)]
lemma config_height (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) :
    let N:=(config δ D F S Δ P κ m M E J).length
    (∀ i j,Height (δ i j) N) ∧ Height P N ∧ Height κ N ∧ n≤N ∧ M≤N ∧ E≤N ∧ J≤N := by
  dsimp only
  have hd : (RationalMatrix.encode δ).length≤(config δ D F S Δ P κ m M E J).length := member_length (by simp)
  have hp : (BinaryRational.encode P).length≤(config δ D F S Δ P κ m M E J).length := member_length (by simp)
  have hk : (BinaryRational.encode κ).length≤(config δ D F S Δ P κ m M E J).length := member_length (by simp)
  have hw : (BinaryMenu.weights M E J).length≤(config δ D F S Δ P κ m M E J).length := member_length (by simp)
  have hM : M≤(BinaryMenu.weights M E J).length := by
    simpa only [BinaryMenu.weights,List.length_replicate] using (member_length (show List.replicate M true∈[List.replicate M true,List.replicate E true,List.replicate J true] by simp))
  have hE : E≤(BinaryMenu.weights M E J).length := by
    simpa only [BinaryMenu.weights,List.length_replicate] using (member_length (show List.replicate E true∈[List.replicate M true,List.replicate E true,List.replicate J true] by simp))
  have hJ : J≤(BinaryMenu.weights M E J).length := by
    simpa only [BinaryMenu.weights,List.length_replicate] using (member_length (show List.replicate J true∈[List.replicate M true,List.replicate E true,List.replicate J true] by simp))
  exact ⟨fun i j=>(RationalMatrix.input_height δ i j).mono hd,(BinaryRational.input_height P).mono hp,
    (BinaryRational.input_height κ).mono hk,(RationalMatrix.dimension_bound δ).trans hd,hM.trans hw,hE.trans hw,hJ.trans hw⟩
lemma runPack_bounds (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ) (seeds : List (Fin b→Bool)) :
    let N:=(runPack (config δ D F S Δ P κ m M E J) m b seeds).length
    (∀ i j,Height (δ i j) N) ∧ Height P N ∧ Height κ N ∧ n≤N ∧ m≤N ∧ M≤N ∧ E≤N ∧ J≤N ∧ seeds.length≤N := by
  dsimp only
  have hc : (config δ D F S Δ P κ m M E J).length≤(runPack (config δ D F S Δ P κ m M E J) m b seeds).length := member_length (by simp)
  have hm : m≤(runPack (config δ D F S Δ P κ m M E J) m b seeds).length := by
    simpa only [runPack,List.length_replicate] using (member_length (show List.replicate m true∈[config δ D F S Δ P κ m M E J,List.replicate m true,List.replicate b true,encode (seeds.map List.ofFn)] by simp))
  have ht : seeds.length≤(encode (seeds.map List.ofFn)).length := by simpa only [List.length_map] using length_le_encode (seeds.map List.ofFn)
  have ht2 : (encode (seeds.map List.ofFn)).length≤(runPack (config δ D F S Δ P κ m M E J) m b seeds).length := member_length (by simp)
  obtain ⟨hd,hp,hk,hn,hM,hE,hJ⟩:=config_height δ D F S Δ P κ m M E J
  exact ⟨fun i j=>(hd i j).mono hc,hp.mono hc,hk.mono hc,hn.trans hc,hm,hM.trans hc,hE.trans hc,hJ.trans hc,ht.trans ht2⟩
noncomputable def capPoly : Polynomial ℕ := 1000*(Polynomial.X+1)^5
noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose _
lemma length_cap (s : Option (RationalSampling.State n)) (m H t : ℕ) (hn : n≤H) (hm : m≤H) (ht : t≤H)
    (hs : ∀ z,s=some z→z.Height (t*RationalSampling.heightIncrement H)) (hb : ∀ z,s=some z→z.Bounded m) :
    (BinarySamplingState.optionBits s).length≤capPoly.eval H := by
  have hh:=BinarySamplingState.option_length s m (t*RationalSampling.heightIncrement H) hs (fun z hz=>(hb z hz).1)
  have hK : t*RationalSampling.heightIncrement H≤H*(10*(H+1)^2) := Nat.mul_le_mul_right _ ht
  have hl : 4*n*(2*n+2)+2*m*(4*n+6*(t*RationalSampling.heightIncrement H)+16)+4≤
      4*H*(2*H+2)+2*H*(4*H+6*(H*(10*(H+1)^2))+16)+4 := by gcongr
  apply hh.trans (hl.trans ?_)
  simp only [capPoly,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith [sq_nonneg (H:ℤ)]
lemma fold_length_cap (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ) (seeds : List (Fin b→Bool)) (j : ℕ) :
    (BinarySamplingState.optionBits ((seeds.take j).foldl (RationalSampling.next δ D F S Δ P κ m M E J b) (some RationalSampling.State.initial))).length≤
      capPoly.eval (runPack (config δ D F S Δ P κ m M E J) m b seeds).length := by
  obtain ⟨hd,hp,hk,hn,hm,hM,hE,hJ,ht⟩:=runPack_bounds δ D F S Δ P κ m M E J b seeds
  apply length_cap _ m _ (seeds.take j).length hn hm ((by simp only [List.length_take];exact Nat.min_le_right _ _ : (seeds.take j).length ≤ seeds.length).trans ht)
  · intro z hz
    have hh:=RationalSampling.fold_next_height δ D F S Δ P κ m M E J b _ 0 hd hp hk hn hm hM hE hJ (seeds.take j)
      (some RationalSampling.State.initial) (fun t ht=>by cases Option.some.inj ht;exact RationalSampling.initial_height 0) z hz
    simpa only [Nat.zero_add] using hh
  · intro z hz
    exact RationalSampling.fold_next_bounded δ D F S Δ P κ m M E J b (seeds.take j) (some RationalSampling.State.initial)
      (fun t ht=>by cases Option.some.inj ht;exact RationalSampling.initial_bounded m) z hz
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
def initial : List Bool := encode [pairBits ([],[])]
lemma initial_eq : initial=BinarySamplingState.optionBits (some (RationalSampling.State.initial (n:=n))) := by
  simp [initial,BinarySamplingState.optionBits,BinarySamplingState.encode,RationalSampling.State.initial,
    BinaryFinSet.encode_eq,BinaryNearestLeaf.leavesBits,WordList.encode]
noncomputable def fixedContext (x : List Bool) : List Bool := pairBits (field 0 x,field 2 x)
noncomputable def fixedContext_computes : PolyComputes fixedContext := (field_computes 0).pair (field_computes 2)
noncomputable def run (x : List Bool) : List Bool :=
  CappedFold.run step (pairBits (cap.word x,Fold.pack (field 3 x) (fixedContext x) initial))
noncomputable def run_computes : PolyComputes run :=
  (cap.computes.pair (Fold.pack_computes (field_computes 3) fixedContext_computes (const_computes initial))).comp
    (CappedFold.run_computes step_computes)
lemma run_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ) (seeds : List (Fin b→Bool)) :
    run (runPack (config δ D F S Δ P κ m M E J) m b seeds)=
      BinarySamplingState.optionBits (seeds.foldl (RationalSampling.next δ D F S Δ P κ m M E J b) (some RationalSampling.State.initial)) := by
  unfold run
  have hc : fixedContext (runPack (config δ D F S Δ P κ m M E J) m b seeds)=
      context (config δ D F S Δ P κ m M E J) b := by
    simp only [fixedContext,runPack,context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have ht : field 3 (runPack (config δ D F S Δ P κ m M E J) m b seeds)=encode (seeds.map List.ofFn) := by
    simp only [runPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hc,ht]
  rw [initial_eq (n:=n)]
  apply CappedFold.run_typed BinarySamplingState.optionBits List.ofFn _ _ _ _ (step_pack δ D F S Δ P κ m M E J b)
  intro j
  rw [cap.word_length]
  exact fold_length_cap δ D F S Δ P κ m M E J b seeds j
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList
attribute [local irreducible] WordList.mapWith
noncomputable def rows (x : List Bool) : List Bool :=
  mapWith (chunk 0) (pairBits (x,indices x))
noncomputable def rows_computes : PolyComputes rows :=
  (id_computes.pair indices_computes).comp (mapWith_computes (chunk_computes 0))
attribute [local irreducible] indices chunk
lemma rows_tensor {t b : ℕ} (s : Fin t→Fin b→Bool) :
    rows (pairBits (shape [t,b],raw (ds:=[t]) s))=encode (List.ofFn (fun i=>List.ofFn (s i))) := by
  have hi : indices (pairBits (shape [t,b],raw (ds:=[t]) s))=encode (List.ofFn (fun i:Fin t=>i.val.bits)) := by
    simp only [indices,extractPrefix_pairBits,shape,List.map_cons,List.map_nil,encode,head_cons]
    exact BinaryEllipsoidInitial.indices_replicate t
  rw [rows,hi,mapWith_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact chunk_tensor t [] b s i
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
