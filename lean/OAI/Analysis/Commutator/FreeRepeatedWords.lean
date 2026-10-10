import Mathlib
import OAI.Analysis.Commutator.FreeCovariance

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace TensorProduct ComplexOrder

open UniformSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι}

def repeatedParams (s : letterSpace t S j) (x : letterSpace t S i)
    (v : factorSpace t S j) : ∀ n, BlockParams t S i j n
  | 0 => v
  | n+1 => ((s,x),repeatedParams s x v n)

@[simp] lemma repeatedParams_D (s : letterSpace t S j) (x : letterSpace t S i)
    (v : factorSpace t S j) (n : ℕ) :
    paramD t S n (repeatedParams t S s x v n)=fun _ => x := by
  induction n with
  | zero => funext k; exact Fin.elim0 k
  | succ n ih =>
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · exact congrFun ih _

def repeatPre (s : letterSpace t S j) : ∀ n,
    factorSpace t S j →ₗ[ℂ] multiplicityTensor t S j n
  | 0 => LinearMap.id
  | n+1 => (TensorProduct.mk ℂ (letterSpace t S j) (multiplicityTensor t S j n) s).comp
      (repeatPre s n)

@[simp] lemma repeatedParams_J (s : letterSpace t S j) (x : letterSpace t S i)
    (v : factorSpace t S j) (n : ℕ) :
    paramJ t S n (repeatedParams t S s x v n)=repeatPre t S s n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change s ⊗ₜ[ℂ] paramJ t S n (repeatedParams t S s x v n)=
      s ⊗ₜ[ℂ] repeatPre t S s n v
    rw [ih]

lemma norm_repeatPre (s : letterSpace t S j) (n : ℕ) (v : factorSpace t S j) :
    ‖repeatPre t S s n v‖=‖s‖^n*‖v‖ := by
  induction n with
  | zero => simp [repeatPre]
  | succ n ih =>
    change ‖s ⊗ₜ[ℂ] repeatPre t S s n v‖=_
    rw [TensorProduct.norm_tmul,ih,pow_succ']
    exact (mul_assoc _ _ _).symm

def repeatPreIsometry (s : letterSpace t S j) (hs : ‖s‖=1) (n : ℕ) :
    factorSpace t S j →ₗᵢ[ℂ] multiplicityTensor t S j n where
  toLinearMap := repeatPre t S s n
  norm_map' v := by rw [norm_repeatPre,hs,one_pow,one_mul]

def repeatInsertion (s : letterSpace t S j) (hs : ‖s‖=1) (n : ℕ) :
    multiplicityLevel t S j 0 →ₗᵢ[ℂ] multiplicityLevel t S j n :=
  HilbertCompletion.map (repeatPreIsometry t S s hs n)

@[simp] lemma repeatInsertion_coe (s : letterSpace t S j) (hs : ‖s‖=1)
    (n : ℕ) (v : factorSpace t S j) :
    repeatInsertion t S s hs n (v : multiplicityLevel t S j 0)=
      (repeatPre t S s n v : multiplicityLevel t S j n) := by
  exact HilbertCompletion.map_coe (repeatPreIsometry t S s hs n) v

@[simp] lemma blockRead_repeated (s : letterSpace t S j) (x : letterSpace t S i)
    (n : ℕ) (v : factorSpace t S j) :
    blockRead t S n (blockPure t S n (repeatedParams t S s x v n))=
      (letterValue t S j s*letterValue t S i x)^n*factorValue t S j v := by
  induction n with
  | zero => simp [repeatedParams,blockPure,blockRead]
  | succ n ih =>
    change letterValue t S j s*(letterValue t S i x*
      blockRead t S n (blockPure t S n (repeatedParams t S s x v n)))=_
    rw [ih,pow_succ']
    simp only [mul_assoc]

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

private def tensorOutput {Left Right Target : Type*}
    [NormedAddCommGroup Left] [InnerProductSpace ℂ Left]
    [NormedAddCommGroup Right] [InnerProductSpace ℂ Right]
    [NormedAddCommGroup Target] [InnerProductSpace ℂ Target]
    (embedding : Completion (Left ⊗[ℂ] Right) →ₗᵢ[ℂ] Target) (vector : Left) :
    Right →L[ℂ] Target :=
  embedding.toContinuousLinearMap.comp (HilbertTensor.insertLeft vector)

private lemma norm_tensorOutput {Left Right Target : Type*}
    [NormedAddCommGroup Left] [InnerProductSpace ℂ Left]
    [NormedAddCommGroup Right] [InnerProductSpace ℂ Right]
    [NormedAddCommGroup Target] [InnerProductSpace ℂ Target]
    (embedding : Completion (Left ⊗[ℂ] Right) →ₗᵢ[ℂ] Target)
    (vector : Left) (value : Right) :
    ‖tensorOutput embedding vector value‖ = ‖vector‖ * ‖value‖ := by
  change ‖embedding (HilbertTensor.pair vector value)‖ = _
  rw [embedding.norm_map, HilbertTensor.norm_pair]

def repeatedOutput (d : D) (x : letterSpace t S i) (n : ℕ) :
    multiplicityLevel t S j n →L[ℂ] t.functional.GNS :=
  tensorOutput (Left := sourceScalar t f hf n) (Right := multiplicityLevel t S j n)
    (sourceLevelEmbedding t f hf S i j hS hfree hij n)
    (PreHilbert.word (factorFull t f hf) (factorZero t f hf) n
      (TracialGNS.algebraVector (factorTrace t f hf) d)
      (fun _ => letterGNSIso t f hf S i hS
        (HilbertCompletion.coeIsometry (dLetters t S i) x)))

lemma repeatedOutput_bounded (d : D) (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (n : ℕ) (v : factorSpace t S j) :
    repeatedOutput t S f hf hS hfree hij d x n
      (repeatInsertion t S s hs n (v : multiplicityLevel t S j 0))=
      t.functional.gnsStarAlgHom (f d)
        (t.functional.gnsStarAlgHom ((letterValue t S j s*letterValue t S i x)^n)
          (blockEmbedding t S hfree hij 0 (v : multiplicityLevel t S j 0))) := by
  have hn : repeatedOutput t S f hf hS hfree hij d x n
      (repeatInsertion t S s hs n (v : multiplicityLevel t S j 0))=
      sourceLevelEmbedding t f hf S i j hS hfree hij n
        (levelWord t f hf S i j hS d n (repeatedParams t S s x v n)) := by
    rw [repeatInsertion_coe]
    simp only [repeatedOutput,tensorOutput,ContinuousLinearMap.comp_apply,HilbertTensor.insertLeft_apply,
      levelWord,repeatedParams_D,repeatedParams_J]
    rfl
  rw [hn,sourceLevelEmbedding_word]
  congr 1
  change (t.functional.toPreGNS
    (blockRead t S n (blockPure t S n (repeatedParams t S s x v n))) : t.functional.GNS)=_
  rw [blockRead_repeated]
  have hv : blockEmbedding t S hfree hij 0 (v : multiplicityLevel t S j 0)=
      (t.functional.toPreGNS (factorValue t S j v) : t.functional.GNS) := by
    simp [blockEmbedding,blockIsometry,blockReadPre,blockRead]
  rw [hv]
  simp [PositiveLinearMap.gnsStarAlgHom]

lemma norm_repeatedOutput_one (x : letterSpace t S i) (hx : ‖x‖=1)
    (n : ℕ) (v : multiplicityLevel t S j n) :
    ‖repeatedOutput t S f hf hS hfree hij 1 x n v‖=‖v‖ := by
  rw [repeatedOutput, norm_tensorOutput]
  have hw := PreHilbert.norm_word (factorFull t f hf)
    (factorZero t f hf) n
    (TracialGNS.algebraVector (factorTrace t f hf) 1)
    (fun _ => letterGNSIso t f hf S i hS
      (HilbertCompletion.coeIsometry (dLetters t S i) x))
  have hnorm : ‖TracialGNS.algebraVector (factorTrace t f hf) 1‖=1 := by
    apply TracialGNS.vacuum_norm
    change t.functional (f 1)=1
    simpa using t.normalized
  have hxnorm : ∀ k : Fin n,
      ‖letterGNSIso t f hf S i hS (HilbertCompletion.coeIsometry (dLetters t S i) x)‖=1 := by
    intro k
    exact (letterGNSIso t f hf S i hS).norm_map _ |>.trans
      ((HilbertCompletion.coeIsometry (dLetters t S i)).norm_map _ |>.trans hx)
  have hw1 : ‖PreHilbert.word (factorFull t f hf)
      (factorZero t f hf) n
      (TracialGNS.algebraVector (factorTrace t f hf) 1)
      (fun _ => letterGNSIso t f hf S i hS
        (HilbertCompletion.coeIsometry (dLetters t S i) x))‖=1 :=
    hw.trans (by rw [hnorm,one_mul]; exact Finset.prod_eq_one (fun k _ => hxnorm k))
  exact (congrArg (fun r : ℝ => r*‖v‖) hw1).trans (one_mul _)

lemma repeatedOutput_inserted (d : D) (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (n : ℕ) (v : multiplicityLevel t S j 0) :
    repeatedOutput t S f hf hS hfree hij d x n
      (repeatInsertion t S s hs n v)=t.functional.gnsStarAlgHom (f d)
        (t.functional.gnsStarAlgHom ((letterValue t S j s*letterValue t S i x)^n)
          (blockEmbedding t S hfree hij 0 v)) := by
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v => exact repeatedOutput_bounded t S f hf hS hfree hij d s hs x n v

lemma repeatedOutput_zero (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (d : D) (v : multiplicityLevel t S j 0) :
    repeatedOutput t S f hf hS hfree hij d x 0 v=
      t.functional.gnsStarAlgHom (f d) (blockEmbedding t S hfree hij 0 v) := by
  have hr : repeatInsertion t S s hs 0 v=v := by
    induction v using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih v => rw [repeatInsertion_coe]; rfl
  simpa [hr] using
    repeatedOutput_inserted t S f hf hS hfree hij d s hs x 0 v

lemma norm_repeatedOutput (d : D) (x : letterSpace t S i)
    (n : ℕ) (v : multiplicityLevel t S j n) :
    ‖repeatedOutput t S f hf hS hfree hij d x n v‖=
      ‖TracialGNS.algebraVector (factorTrace t f hf) d‖*‖x‖^n*‖v‖ := by
  rw [repeatedOutput, norm_tensorOutput]
  have hw := PreHilbert.norm_word (factorFull t f hf)
    (factorZero t f hf) n
    (TracialGNS.algebraVector (factorTrace t f hf) d)
    (fun _ => letterGNSIso t f hf S i hS
      (HilbertCompletion.coeIsometry (dLetters t S i) x))
  have hxnorm (k : Fin n) : ‖letterGNSIso t f hf S i hS
      (HilbertCompletion.coeIsometry (dLetters t S i) x)‖ = ‖x‖ := by
    exact (letterGNSIso t f hf S i hS).norm_map _ |>.trans
      ((HilbertCompletion.coeIsometry (dLetters t S i)).norm_map _)
  have hprod : ∏ k : Fin n, ‖letterGNSIso t f hf S i hS
      (HilbertCompletion.coeIsometry (dLetters t S i) x)‖ = ‖x‖^n := by
    calc
      _ = ∏ _k : Fin n, ‖x‖ := Finset.prod_congr rfl (fun k _ => hxnorm k)
      _ = _ := by simp
  exact congrArg (fun r : ℝ => r*‖v‖)
    (hw.trans (congrArg (fun r : ℝ => ‖TracialGNS.algebraVector (factorTrace t f hf) d‖*r) hprod))

include hS in
lemma norm_base_mul (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (d : D) (v : multiplicityLevel t S j 0) :
    ‖t.functional.gnsStarAlgHom (f d) (blockEmbedding t S hfree hij 0 v)‖=
      ‖TracialGNS.algebraVector (factorTrace t f hf) d‖*‖v‖ := by
  rw [←repeatedOutput_zero t S f hf hS hfree hij s hs x d v,
    norm_repeatedOutput]
  simp

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

variable (hB : ∀ n d (x : letterSpace t S i) v,
  G (repeatedOutput t S f hf hS hfree hij d x n v)=
    repeatedOutput t S f hf hS hfree hij d x n (B n v))

include hB in
lemma base_intertwining (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (d : D) (v : multiplicityLevel t S j 0) :
    G (t.functional.gnsStarAlgHom (f d) (blockEmbedding t S hfree hij 0 v))=
      t.functional.gnsStarAlgHom (f d) (blockEmbedding t S hfree hij 0 (B 0 v)) := by
  simpa only [repeatedOutput_zero t S f hf hS hfree hij s hs x] using hB 0 d x v

include hB in
lemma repeated_error_norm (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (hx : ‖x‖=1) (n : ℕ) (v : multiplicityLevel t S j 0) :
    ‖G (t.functional.gnsStarAlgHom ((letterValue t S j s*letterValue t S i x)^n)
        (blockEmbedding t S hfree hij 0 v))-
      t.functional.gnsStarAlgHom ((letterValue t S j s*letterValue t S i x)^n)
        (blockEmbedding t S hfree hij 0 (B 0 v))‖=
    ‖B n (repeatInsertion t S s hs n v)-repeatInsertion t S s hs n (B 0 v)‖ := by
  have hout (z : multiplicityLevel t S j 0) :
      repeatedOutput t S f hf hS hfree hij 1 x n (repeatInsertion t S s hs n z)=
      t.functional.gnsStarAlgHom ((letterValue t S j s*letterValue t S i x)^n)
        (blockEmbedding t S hfree hij 0 z) := by
    simpa using repeatedOutput_inserted t S f hf hS hfree hij 1 s hs x n z
  rw [←hout v,←hout (B 0 v),hB,←map_sub]
  exact norm_repeatedOutput_one t S f hf hS hfree hij x hx n _

include hf hS in
lemma repeated_norm (s : letterSpace t S j) (hs : ‖s‖=1)
    (x : letterSpace t S i) (hx : ‖x‖=1) (n : ℕ) (v : multiplicityLevel t S j 0) :
    ‖t.functional.gnsStarAlgHom ((letterValue t S j s*letterValue t S i x)^n)
        (blockEmbedding t S hfree hij 0 v)‖=‖v‖ := by
  have hout := repeatedOutput_inserted t S f hf hS hfree hij 1 s hs x n v
  simp only [map_one,one_apply_eq_self] at hout
  rw [←hout,norm_repeatedOutput_one t S f hf hS hfree hij x hx,
    (repeatInsertion t S s hs n).norm_map]

end Kadison.FreeBlocks

end

end
end

end OAI
