import OAI.Analysis.Naimark.Amalgamation

namespace OAI

noncomputable section

namespace NaimarkZFC

section
open scoped CStarAlgebra
variable {A B Z : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra Z]

@[simp] theorem matrixSingle_add {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) (a b : A) : matrixSingle i j (a+b) = matrixSingle i j a + matrixSingle i j b := by
  ext k l
  by_cases h : i = k ∧ j = l <;> simp [h]

variable (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)

def matrixCornerProjection : Z := φ (matrixSingle false false (1 : A))

theorem matrixCornerProjection_isProjection : IsStarProjection (matrixCornerProjection φ) :=
  (matrixSingle_projection false (1 : A) (IsStarProjection.one A)).map φ

abbrev MatrixHNNCorner := CStarCorner (matrixCornerProjection φ)
  (matrixCornerProjection_isProjection φ)

def matrixCornerBase : A →⋆ₐ[ℂ] MatrixHNNCorner φ where
  toFun a := ⟨φ (matrixSingle false false a), by
    constructor
    · change φ (matrixSingle false false (1 : A)) * φ (matrixSingle false false a) = _
      rw [← map_mul, matrixSingle_mul, one_mul]
    · change φ (matrixSingle false false a) * φ (matrixSingle false false (1 : A)) = _
      rw [← map_mul, matrixSingle_mul, mul_one]⟩
  map_zero' := Subtype.ext (by
    change φ (matrixSingle false false (0 : A)) = 0
    simp)
  map_one' := rfl
  map_add' a b := Subtype.ext (by
    change φ (matrixSingle false false (a+b)) = φ (matrixSingle false false a) + φ (matrixSingle false false b)
    simp)
  map_mul' a b := Subtype.ext (by
    change φ (matrixSingle false false (a*b)) = φ (matrixSingle false false a) * φ (matrixSingle false false b)
    rw [← map_mul, matrixSingle_mul])
  commutes' z := Subtype.ext (by
    change φ (matrixSingle false false (algebraMap ℂ A z)) = z • matrixCornerProjection φ
    rw [Algebra.algebraMap_eq_smul_one, matrixSingle_smul, map_smul]
    rfl)
  map_star' a := Subtype.ext (by
    change φ (matrixSingle false false (star a)) = star (φ (matrixSingle false false a))
    rw [← map_star, matrixSingle_star])

@[simp] theorem matrixCornerBase_coe (a : A) :
    (matrixCornerBase φ a : Z) = φ (matrixSingle false false a) := rfl

theorem matrixCornerBase_injective (hφ : Function.Injective φ) :
    Function.Injective (matrixCornerBase φ) := by
  intro a b hab
  have h := hφ (congrArg Subtype.val hab)
  have h' := congrArg (fun M : CStarMatrix Bool Bool A => M false false) h
  simpa only [matrixSingle_apply, and_self, ite_true] using h'

variable (ψ : CStarMatrix Bool Bool B →⋆ₐ[ℂ] Z)
  (diag : ∀ i : Bool, φ (matrixSingle i i (1 : A)) = ψ (matrixSingle i i (1 : B)))

def matrixStableElement : Z := φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))

include diag in
theorem matrixStableElement_mem : matrixStableElement φ ψ ∈ cornerSubalgebra
    (matrixCornerProjection φ) (matrixCornerProjection_isProjection φ) := by
  constructor
  · change φ (matrixSingle false false (1 : A)) * (φ _ * ψ _) = φ _ * ψ _
    rw [← mul_assoc, ← map_mul, matrixSingle_mul, one_mul]
  · change (φ _ * ψ _) * φ (matrixSingle false false (1 : A)) = φ _ * ψ _
    rw [mul_assoc, diag false, ← map_mul, matrixSingle_mul, one_mul]

def matrixStable : MatrixHNNCorner φ := ⟨matrixStableElement φ ψ, matrixStableElement_mem φ ψ diag⟩

include diag in
theorem matrixStable_star_mul : star (matrixStable φ ψ diag) * matrixStable φ ψ diag = 1 := by
  apply Subtype.ext
  change star (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) *
    (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) =
    φ (matrixSingle false false (1 : A))
  simp only [star_mul, ← map_star, matrixSingle_star, star_one]
  rw [mul_assoc, ← mul_assoc (φ _), ← map_mul, matrixSingle_mul, one_mul, diag true,
    ← map_mul, matrixSingle_mul, one_mul, ← map_mul, matrixSingle_mul, one_mul, diag false]

include diag in
theorem matrixStable_mul_star : matrixStable φ ψ diag * star (matrixStable φ ψ diag) = 1 := by
  apply Subtype.ext
  change (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) *
    star (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) =
    φ (matrixSingle false false (1 : A))
  simp only [star_mul, ← map_star, matrixSingle_star, star_one]
  rw [mul_assoc, ← mul_assoc (ψ _), ← map_mul, matrixSingle_mul, one_mul, ← diag true,
    ← map_mul, matrixSingle_mul, one_mul, ← map_mul, matrixSingle_mul, one_mul]

def matrixStableUnitary : unitary (MatrixHNNCorner φ) :=
  ⟨matrixStable φ ψ diag, matrixStable_star_mul φ ψ diag, matrixStable_mul_star φ ψ diag⟩

theorem matrixDiagonalHom_single (δ : Bool → B →⋆ₐ[ℂ] A) (i : Bool) (b : B) :
    matrixDiagonalHom δ (Pi.single i b) = matrixSingle i i (δ i b) := by
  ext k l
  cases i <;> cases k <;> cases l <;> simp

variable (δ : Bool → B →⋆ₐ[ℂ] A)
  (hδ : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ B) x))

include hδ in
theorem matrixDiagonal_agrees (i : Bool) (b : B) :
    φ (matrixSingle i i (δ i b)) = ψ (matrixSingle i i b) := by
  have h := hδ (Pi.single i b)
  rw [matrixDiagonalHom_single, matrixDiagonalHom_single] at h
  exact h

include hδ in
theorem matrixDiagonal_units (i : Bool) :
    φ (matrixSingle i i (1 : A)) = ψ (matrixSingle i i (1 : B)) := by
  simpa only [map_one] using matrixDiagonal_agrees φ ψ δ hδ i 1

include hδ in

theorem matrixStable_conjugates (b : B) :
    matrixStable φ ψ (matrixDiagonal_units φ ψ δ hδ) * matrixCornerBase φ (δ false b) *
      star (matrixStable φ ψ (matrixDiagonal_units φ ψ δ hδ)) =
    matrixCornerBase φ (δ true b) := by
  apply Subtype.ext
  change (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) *
    φ (matrixSingle false false (δ false b)) *
    star (φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true false (1 : B))) =
    φ (matrixSingle false false (δ true b))
  simp only [star_mul, ← map_star, matrixSingle_star, star_one]
  rw [matrixDiagonal_agrees φ ψ δ hδ false b]
  calc
    _ = φ (matrixSingle false true (1 : A)) *
      (ψ (matrixSingle true false (1 : B)) * ψ (matrixSingle false false b) *
        ψ (matrixSingle false true (1 : B))) * φ (matrixSingle true false (1 : A)) := by
      simp only [mul_assoc]
    _ = φ (matrixSingle false true (1 : A)) * ψ (matrixSingle true true b) *
        φ (matrixSingle true false (1 : A)) := by
      rw [← map_mul, matrixSingle_mul, one_mul, ← map_mul, matrixSingle_mul, mul_one]
    _ = _ := by
      rw [← matrixDiagonal_agrees φ ψ δ hδ true b,
        ← map_mul, matrixSingle_mul, one_mul, ← map_mul, matrixSingle_mul, mul_one]

end

open scoped ComplexOrder CStarAlgebra
section
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n]

def matrixSingleHom (i : n) : A →⋆ₙₐ[ℂ] CStarMatrix n n A where
  toFun := matrixSingle i i
  map_zero' := matrixSingle_zero i i
  map_add' a b := by ext k l; simp only [matrixSingle_apply, CStarMatrix.add_apply]; split_ifs <;> simp
  map_mul' a b := (matrixSingle_mul i i i a b).symm
  map_smul' z a := matrixSingle_smul i i a z
  map_star' a := (matrixSingle_star i i a).symm

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem matrixSingleHom_apply (i : n) (a : A) :
    matrixSingleHom i a = matrixSingle i i a := rfl

def matrixSinglePositive (i : n) : A →ₚ[ℂ] CStarMatrix n n A :=
  PositiveLinearMap.mk₀
    { toFun := matrixSingle i i
      map_add' a b := map_add (matrixSingleHom i) a b
      map_smul' z a := matrixSingle_smul i i a z } (by
    intro a ha
    change 0 ≤ matrixSingleHom i a
    exact AddSubmonoid.closure_induction (motive := fun a _ => 0 ≤ matrixSingleHom i a)
      (by rintro a ⟨b,rfl⟩; rw [map_mul,map_star]; exact star_mul_self_nonneg _)
      (by rw [map_zero])
      (by intro a b _ _ ha hb; rw [map_add]; exact add_nonneg ha hb) (StarOrderedRing.nonneg_iff.mp ha))

def matrixEntryPositive (i : n) : CStarMatrix n n A →ₚ[ℂ] A :=
  PositiveLinearMap.mk₀
    { toFun := fun M => M i i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (by
      intro M hM
      apply AddSubmonoid.closure_induction
        (motive := fun M _ => 0 ≤ M i i) ?_ ?_ ?_
        (StarOrderedRing.nonneg_iff.mp hM)
      · rintro M ⟨N,rfl⟩
        simp only [CStarMatrix.mul_apply,CStarMatrix.star_apply]
        exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg _
      · exact le_rfl
      · intro M N _ _ hM hN; exact add_nonneg hM hN)

def matrixEntryCLM (i : n) : CStarMatrix n n A →L[ℂ] A :=
  (matrixEntryPositive i).toLinearMap.mkContinuous 1 (fun M => by
    change ‖M i i‖ ≤ 1 * ‖M‖
    simpa only [one_mul] using (CStarMatrix.norm_entry_le_norm (M := M) (i := i) (j := i)))

def matrixSingleCLM (i : n) : A →L[ℂ] CStarMatrix n n A :=
  (matrixSinglePositive i).toLinearMap.mkContinuous 1 (fun a => by
    change ‖matrixSingleHom i a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le (matrixSingleHom i) a)

def matrixState (f : A →L[ℂ] ℂ) (i : n) : CStarMatrix n n A →L[ℂ] ℂ :=
  f.comp (matrixEntryCLM i)

omit [DecidableEq n] in
@[simp] theorem matrixState_apply (f : A →L[ℂ] ℂ) (i : n) (M : CStarMatrix n n A) :
    matrixState f i M = f (M i i) := rfl

theorem matrixState_isState (f : A →L[ℂ] ℂ) (hf : IsState f) (i : n) :
    IsState (matrixState f i) := by
  apply (isState_iff _).mpr
  constructor
  · simpa only [matrixState_apply,CStarMatrix.one_apply_eq] using ((isState_iff f).mp hf).1
  · intro M
    have h := state_nonneg f hf ((matrixEntryPositive i).map_nonneg (star_mul_self_nonneg M))
    exact ⟨h.2.symm,h.1⟩

theorem matrix_state_supported (g : CStarMatrix n n A →L[ℂ] ℂ) (hg : IsState g)
    (i : n) (hi : g (matrixSingle i i (1 : A)) = 1) (M : CStarMatrix n n A) :
    g M = g (matrixSingle i i (M i i)) := by
  have he := state_compression g hg (matrixSingle i i 1)
    ((matrixSingle_projection i 1 (by constructor <;> simp [IsIdempotentElem, IsSelfAdjoint])).norm_le _)
    (matrixSingle_projection i 1 (by constructor <;> simp [IsIdempotentElem, IsSelfAdjoint])).isSelfAdjoint hi M
  rw [matrixSingle_compress,one_mul,mul_one] at he
  exact he.symm

theorem matrix_corner_isState (g : CStarMatrix n n A →L[ℂ] ℂ) (hg : IsState g)
    (i : n) (hi : g (matrixSingle i i (1 : A)) = 1) :
    IsState (g.comp (matrixSingleCLM i)) := by
  apply (isState_iff _).mpr
  refine ⟨hi, ?_⟩
  intro a
  have h := state_nonneg g hg ((matrixSinglePositive i).map_nonneg (star_mul_self_nonneg a))
  exact ⟨h.2.symm,h.1⟩

theorem Peaks.matrix {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (i : n) : Peaks (fun k => matrixSingle i i (p k)) (matrixState f i) := by
  refine ⟨fun k => matrixSingle_projection i _ (hp.1 k), ?_, matrixState_isState f hp.2.2.1 i,
    ?_, ?_⟩
  · intro k l hkl
    exact (matrixSinglePositive i).monotone (hp.2.1 hkl)
  · intro k
    simp [hp.2.2.2.1 k]
  · intro g hg hgp
    have hgi : g (matrixSingle i i (1 : A)) = 1 := by simpa only [hp0] using hgp 0
    have hc := hp.2.2.2.2 (g.comp (matrixSingleCLM i))
      (matrix_corner_isState g hg i hgi) hgp
    ext M
    rw [matrix_state_supported g hg i hgi M,matrixState_apply]
    exact congrArg (fun k : A →L[ℂ] ℂ => k (M i i)) hc

end

open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint
section
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n]

def matrixTraceState (τ : A →L[ℂ] ℂ) (hτ : IsState τ) : CStarMatrix n n A →L[ℂ] ℂ :=
  positiveCLM (normalizedMatrixTrace (positiveOfSquares τ hτ.2))

theorem matrixTraceState_isState (τ : A →L[ℂ] ℂ) (hτ : IsState τ) :
    IsState (matrixTraceState (n := n) τ hτ) := by
  apply (isState_iff _).mpr
  refine ⟨normalizedMatrixTrace_one _ ((isState_iff τ).mp hτ).1, ?_⟩
  intro M
  have h := (normalizedMatrixTrace (n := n) (positiveOfSquares τ hτ.2)).map_nonneg
    (star_mul_self_nonneg M)
  exact ⟨h.2.symm,h.1⟩

omit [Nonempty n] in
theorem matrixTraceState_tracial (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (M N : CStarMatrix n n A) :
    matrixTraceState τ hτ (M*N) = matrixTraceState τ hτ (N*M) :=
  normalizedMatrixTrace_tracial (positiveOfSquares τ hτ.2) htr M N

omit [Nonempty n] in
@[simp] theorem matrixTraceState_single (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (i : n) (a : A) :
    matrixTraceState τ hτ (matrixSingle i i a) = (Fintype.card n : ℝ)⁻¹ • τ a :=
  normalizedMatrixTrace_single _ i a

omit [Nonempty n] in
@[simp] theorem matrix_peakAtom (p : ℕ → A) (i : n) (m : ℕ) :
    peakAtom (fun k => matrixSingle i i (p k)) m = matrixSingle i i (peakAtom p m) :=
  (map_sub (matrixSingleHom i) (p m) (p (m+1))).symm

theorem matrix_cornerState (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (i : n) (q : A)
    (M : CStarMatrix n n A) :
    cornerState (matrixTraceState τ hτ) (matrixSingle i i q) M = cornerState τ q (M i i) := by
  rw [cornerState_apply,cornerState_apply,matrixSingle_compress,
    matrixTraceState_single,matrixTraceState_single,Complex.smul_re,smul_eq_mul,
    mul_inv_rev,smul_smul]
  have hc : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  congr 1
  rw [mul_assoc, inv_inv, mul_inv_cancel₀ hc,mul_one]

variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
  (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ k, 0 < (τ (peakAtom p k)).re)

include hpos in
theorem matrix_peakAtom_positive (i : n) (k : ℕ) :
    0 < (matrixTraceState τ hτ (peakAtom (fun m => matrixSingle i i (p m)) k)).re := by
  rw [matrix_peakAtom,matrixTraceState_single,Complex.smul_re,smul_eq_mul]
  exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)) (hpos k)

theorem matrix_peakingCoefficients (i : n) (M : CStarMatrix n n A) :
    peakingCoefficients (hp.matrix hp0 i) (matrixTraceState τ hτ)
      (matrixTraceState_isState τ hτ) (matrix_peakAtom_positive τ hτ hpos i) M =
      peakingCoefficients hp τ hτ hpos (M i i) := by
  ext t
  induction t using OnePoint.rec with
  | infty => rfl
  | coe k =>
    rw [peakingCoefficients_nat,peakingCoefficients_nat,matrix_peakAtom]
    exact matrix_cornerState τ hτ i _ M

end

section
variable {A n ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n] [Preorder ι]
  {p : n → ℕ → A} {f : n → A →L[ℂ] ℂ}
  (hp : ∀ j, Peaks (p j) (f j)) (hp0 : ∀ j, p j 0 = 1)
  (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ j k, 0 < (τ (peakAtom (p j) k)).re)

theorem matrix_endpoint_decay (i : n) (M : ι → CStarMatrix n n A)
    (ht : Tendsto (fun k => peakingCoefficients ((hp i).matrix (hp0 i) i)
      (matrixTraceState τ hτ) (matrixTraceState_isState τ hτ)
      (matrix_peakAtom_positive τ hτ (hpos i) i) (M k)) atTop (𝓝 0)) :
    Tendsto (fun k => matrixDiagonalExpectation
      (fun j => peakingCoefficients (hp j) τ hτ (hpos j))
      (fun j a => peakingCoefficientsFun_norm_le (hp j) τ hτ (hpos j) a)
      (matrixSingle i i 1 * M k * matrixSingle i i 1)) atTop (𝓝 0) := by
  have ht' : Tendsto (fun k => peakingCoefficients (hp i) τ hτ (hpos i) (M k i i))
      atTop (𝓝 0) := by
    simpa only [matrix_peakingCoefficients (hp i) (hp0 i) τ hτ (hpos i)] using ht
  apply tendsto_pi_nhds.mpr
  intro j
  change Tendsto (fun k => peakingCoefficients (hp j) τ hτ (hpos j)
    (((matrixSingle i i (1 : A) * M k * matrixSingle i i (1 : A)) : CStarMatrix n n A) j j)) atTop (𝓝 0)
  simp only [matrixSingle_compress,one_mul,mul_one,matrixSingle_apply,and_self]
  by_cases hji : i = j
  · subst j
    simpa only [ite_true] using ht'
  · simpa only [hji,ite_false,map_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : SequenceDiagonal)) atTop (𝓝 0))

end

section
variable {C : Type*} [CStarAlgebra C]

theorem two_end_norm_bound (P d w d' : C) (hP : IsStarProjection P)
    (hw : (1-P)*w*(1-P) = 0) :
    ‖d*w*d'‖ ≤ ‖d*P‖*‖w‖*‖d'‖ + ‖d‖*‖w‖*‖P*d'‖ := by
  have hdecomp : w = P*w+(1-P)*w*P := by
    have hh : w - (P*w+(1-P)*w*P) = (1-P)*w*(1-P) := by noncomm_ring
    rw [hw] at hh
    exact sub_eq_zero.mp hh
  calc
    ‖d*w*d'‖ = ‖d*(P*w)*d'+d*((1-P)*w*P)*d'‖ := by
      conv_lhs => rw [hdecomp]
      rw [mul_add, add_mul]
    _ ≤ ‖d*(P*w)*d'‖+‖d*((1-P)*w*P)*d'‖ := norm_add_le _ _
    _ = ‖(d*P)*w*d'‖+‖(d*(1-P))*w*(P*d')‖ := by simp only [mul_assoc]
    _ ≤ ‖d*P‖*‖w‖*‖d'‖ + ‖d*(1-P)‖*‖w‖*‖P*d'‖ :=
      add_le_add norm_mul₃_le norm_mul₃_le
    _ ≤ ‖d*P‖*‖w‖*‖d'‖ + ‖d‖*‖w‖*‖P*d'‖ := by
      gcongr
      calc
        ‖d*(1-P)‖ ≤ ‖d‖*‖1-P‖ := norm_mul_le _ _
        _ ≤ ‖d‖*1 := mul_le_mul_of_nonneg_left (hP.one_sub.norm_le _) (norm_nonneg _)
        _ = ‖d‖ := mul_one _

variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

theorem fockStartProjection_isProjection (i : I) : IsStarProjection (fockStartProjection L i) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    ext j
    simp only [mul_apply_eq_comp, fockStartProjection_apply]
    split_ifs <;> rfl
  · exact fockStartProjection_star L i

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (d : ∀ i, AtomicTraceData (A i) V)

theorem atomicLeft_start_bound {i j : I} (hij : i ≠ j) (a : A i) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ r, ((d i).trace (((d i).atom r).1 * (star a*a) * ((d i).atom r).1)).re ≤
      C^2*((d i).trace ((d i).atom r).1).re) :
    ‖atomicLeft d i a * fockStartProjection (AtomicLetters d) j‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  change ‖atomicLeft d i a (fockStartProjection (AtomicLetters d) j x)‖ ≤ C*‖x‖
  calc
    _ ≤ C * ‖fockStartProjection (AtomicLetters d) j x‖ :=
      atomicLeft_away_norm d i a C hC ha _
        (fockStarts_away _ hij.symm _ (fockStartProjection_starts _ _ _))
    _ ≤ C * (1*‖x‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.le_of_opNorm_le _ (fockStartProjection_norm_le _ _) _) hC
    _ = C*‖x‖ := by rw [one_mul]

end

open Filter Topology
open scoped ComplexOrder
section
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
  {Δ : Type*} [CStarAlgebra Δ] (c : AtomicAmalgamData (Δ := Δ) d)

omit [DecidableEq I] [DecidableEq V] in

theorem atomicCoordinate_norm_le (x : Δ) (r : V) : ‖c.coordinate x r‖ ≤ ‖x‖ := by
  let i := c.base
  let q : A i := ((d i).atom r).1
  have hq : 0 < ‖q‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hp := (d i).positive r
    change 0 < ((d i).trace q).re at hp
    rw [hz, map_zero, Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  apply (mul_le_mul_iff_right₀ hq).mp
  calc
    ‖q‖ * ‖c.coordinate x r‖ = ‖c.coordinate x r • q‖ := by rw [norm_smul,mul_comm]
    _ = ‖q * c.diagonal i x‖ := congrArg norm (c.atom_mul i x r).symm
    _ ≤ ‖q‖ * ‖c.diagonal i x‖ := norm_mul_le _ _
    _ ≤ ‖q‖ * ‖x‖ := mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le _ _) hq.le

omit [DecidableEq I] [DecidableEq V] in

theorem atomicExpectation_corner_formula (i : I) (a : A i) (r : V) :
    (d i).trace (((d i).atom r).1*a*((d i).atom r).1) =
      c.coordinate (c.expectation i a) r * (d i).trace ((d i).atom r).1 := by
  have hz := c.centered i (a-c.diagonal i (c.expectation i a)) (by rw [map_sub,c.fix,sub_self]) r
  rw [mul_sub,sub_mul,map_sub,c.atom_mul,smul_mul_assoc,
    ((d i).atom r).2.isIdempotentElem.eq,map_smul] at hz
  exact sub_eq_zero.mp hz

omit [DecidableEq V] in

theorem atomicLeft_expectation_bound {i j : I} (hij : i ≠ j) (a : A i) :
    ‖atomicLeft d i a * fockStartProjection (AtomicLetters d) j‖ ≤
      Real.sqrt ‖c.expectation i (star a*a)‖ := by
  apply atomicLeft_start_bound d hij a _ (Real.sqrt_nonneg _)
  intro r
  rw [Real.sq_sqrt (norm_nonneg _), atomicExpectation_corner_formula d c]
  have hp := (d i).trace.map_nonneg ((d i).atom r).2.nonneg
  rw [Complex.mul_re, ← hp.2, Complex.zero_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_right
    ((Complex.re_le_norm _).trans (atomicCoordinate_norm_le d c _ r)) ((d i).positive r).le

omit [DecidableEq V] in

theorem atomicLeft_expectation_bound_right {i j : I} (hij : i ≠ j) (a : A i) :
    ‖fockStartProjection (AtomicLetters d) j * atomicLeft d i a‖ ≤
      Real.sqrt ‖c.expectation i (a*star a)‖ := by
  have h := atomicLeft_expectation_bound d c hij (star a)
  rw [star_star, map_star, ← fockStartProjection_star (AtomicLetters d) j,
    ← star_mul] at h
  change ‖(fockStartProjection (AtomicLetters d) j * atomicLeft d i a).adjoint‖ ≤ _ at h
  rw [LinearIsometryEquiv.norm_map] at h
  exact h

end

section
variable {C : Type*} [CStarAlgebra C] {ι : Type*} {l : Filter ι}

theorem two_end_tendsto (P w : C) (hP : IsStarProjection P)
    (hw : (1-P)*w*(1-P) = 0) (d e : ι → C) (L R : ℝ)
    (hd : ∀ i, ‖d i‖ ≤ L) (he : ∀ i, ‖e i‖ ≤ R)
    (hlt : Tendsto (fun i => d i*P) l (𝓝 0))
    (hrt : Tendsto (fun i => P*e i) l (𝓝 0)) :
    Tendsto (fun i => d i*w*e i) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _)
    (g := fun i => ‖d i*P‖*‖w‖*R+L*‖w‖*‖P*e i‖)
  · intro i
    apply (two_end_norm_bound P (d i) w (e i) hP hw).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (he i) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hd i) (norm_nonneg _))
        (norm_nonneg _))
  · simpa only [norm_zero,zero_mul,mul_zero,zero_add] using
      ((hlt.norm.mul_const ‖w‖).mul_const R).add (hrt.norm.const_mul (L*‖w‖))
end

open Filter Topology
section
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
  {Δ : Type*} [CStarAlgebra Δ] (c : AtomicAmalgamData (Δ := Δ) d)
  {ι : Type*} {l : Filter ι}

omit [DecidableEq V] in

theorem atomicLeft_endpoint_tendsto {i j : I} (hij : i ≠ j) (a : ι → A i)
    (ha : Tendsto (fun k => c.expectation i (star (a k)*a k)) l (𝓝 0)) :
    Tendsto (fun k => atomicLeft d i (a k)*fockStartProjection (AtomicLetters d) j)
      l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _) (fun k => atomicLeft_expectation_bound d c hij (a k))
  simpa only [norm_zero, Real.sqrt_zero] using ha.norm.sqrt

omit [DecidableEq V] in

theorem atomicLeft_endpoint_tendsto_right {i j : I} (hij : i ≠ j) (a : ι → A i)
    (ha : Tendsto (fun k => c.expectation i (a k*star (a k))) l (𝓝 0)) :
    Tendsto (fun k => fockStartProjection (AtomicLetters d) j*atomicLeft d i (a k))
      l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _)
    (fun k => atomicLeft_expectation_bound_right d c hij (a k))
  simpa only [norm_zero, Real.sqrt_zero] using ha.norm.sqrt

omit [DecidableEq V] in

theorem atomic_core_endpoint_decay {i j : I} (hij : i ≠ j)
    (w : AtomicFockSpace (AtomicLetters d) →L[ℂ] AtomicFockSpace (AtomicLetters d))
    (hw : (1-fockStartProjection (AtomicLetters d) j)*w*
      (1-fockStartProjection (AtomicLetters d) j) = 0)
    (a b : ι → A i) (L R : ℝ) (ha : ∀ k, ‖a k‖ ≤ L) (hb : ∀ k, ‖b k‖ ≤ R)
    (hlt : Tendsto (fun k => c.expectation i (star (a k)*a k)) l (𝓝 0))
    (hrt : Tendsto (fun k => c.expectation i (b k*star (b k))) l (𝓝 0)) :
    Tendsto (fun k => atomicLeft d i (a k)*w*atomicLeft d i (b k)) l (𝓝 0) := by
  refine two_end_tendsto _ w (fockStartProjection_isProjection _ _) hw _ _ L R ?_ ?_
    (atomicLeft_endpoint_tendsto d c hij a hlt) (atomicLeft_endpoint_tendsto_right d c hij b hrt)
  · intro k
    exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans (ha k)
  · intro k
    exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans (hb k)

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint
section
variable {A n ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n] [Preorder ι]
  {p : n → ℕ → A} {f : n → A →L[ℂ] ℂ}
  (hp : ∀ j, Peaks (p j) (f j)) (hp0 : ∀ j, p j 0 = 1)
  (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ j k, 0 < (τ (peakAtom (p j) k)).re)

def matrixPeakingExpectation : CStarMatrix n n A →L[ℂ] (n → SequenceDiagonal) :=
  matrixDiagonalExpectation (fun j => peakingCoefficients (hp j) τ hτ (hpos j))
    (fun j a => peakingCoefficientsFun_norm_le (hp j) τ hτ (hpos j) a)

theorem matrix_excision_square_endpoint
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (i : n)
    (h : CStarMatrix n n A →L[ℂ] ℂ) (hh : IsPureState h)
    (x : ι → CStarMatrix n n A) (hx : ∀ k, 0 ≤ x k) (hxn : ∀ k, ‖x k‖ ≤ 1)
    (hm : Antitone x)
    (htrace : Tendsto (fun k => matrixTraceState τ hτ (x k)) atTop (𝓝 0))
    (hexc : ∀ b : CStarMatrix n n A,
      Tendsto (fun k => x k*(b-h b • (1:CStarMatrix n n A))*x k) atTop (𝓝 0))
    (a : CStarMatrix n n A)
    (hcase : ¬ UnitarilyEquivalent (pureGNS h hh)
        (pureGNS (matrixState (f i) i) ((hp i).matrix (hp0 i) i).isPureState) ∨
      h = matrixState (f i) i ∧ matrixState (f i) i a = 0) :
    Tendsto (fun k => matrixPeakingExpectation hp τ hτ hpos
      (star (x k*a*matrixSingle i i 1)*(x k*a*matrixSingle i i 1))) atTop (𝓝 0) := by
  have ht := peaking_endpoint_of_excision ((hp i).matrix (hp0 i) i) h hh
    (matrixTraceState τ hτ) (matrixTraceState_isState τ hτ)
    (matrixTraceState_tracial τ hτ htr)
    (matrix_peakAtom_positive τ hτ (hpos i) i) x hx hxn hm htrace hexc a hcase
  have hwhole := matrix_endpoint_decay hp hp0 τ hτ hpos i
    (fun k => star a*(x k*x k)*a) ht
  have he (k : ι) : star (x k*a*matrixSingle i i (1:A))*(x k*a*matrixSingle i i (1:A)) =
      matrixSingle i i (1:A)*(star a*(x k*x k)*a)*matrixSingle i i (1:A) := by
    rw [star_mul,star_mul,matrixSingle_star,star_one,(IsSelfAdjoint.of_nonneg (hx k)).star_eq]
    simp only [mul_assoc]
  simpa only [he,matrixPeakingExpectation] using hwhole

omit [DecidableEq n] [Nonempty n] in

theorem matrix_centered_state_zero (a : CStarMatrix n n A)
    (ha : matrixPeakingExpectation hp τ hτ hpos a = 0) (i : n) :
    matrixState (f i) i a = 0 := by
  have he : peakingCoefficients (hp i) τ hτ (hpos i) (a i i) = 0 := congrFun ha i
  exact congrArg (fun g : SequenceDiagonal => g ∞) he

end

open Filter Topology
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Peaks.rectangular_excision {p : ℕ → A} {f : A →L[ℂ] ℂ}
    (hp : Peaks p f) (a : A) (ha : f a = 0) :
    Tendsto (fun nt : ℕ × ℕ => p nt.1*a*p nt.2) atTop (𝓝 0) := by
  have hmin : Tendsto (fun nt : ℕ × ℕ => min nt.1 nt.2) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact eventually_atTop.2 ⟨(n,n), fun _ h => le_min h.1 h.2⟩
  have hc : Tendsto (fun n => ‖p n*a*p n‖) atTop (𝓝 0) := by
    simpa only [ha,zero_smul,sub_zero] using hp.excision a
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (g := fun nt : ℕ × ℕ => ‖p (min nt.1 nt.2)*a*p (min nt.1 nt.2)‖) ?_ (hc.comp hmin)
  intro nt
  let q := min nt.1 nt.2
  have he : p nt.1*(p q*a*p q)*p nt.2 = p nt.1*a*p nt.2 := by
    calc
      _ = (p nt.1*p q)*a*(p q*p nt.2) := by simp only [mul_assoc]
      _ = _ := by rw [hp.mul_peak,hp.mul_peak,max_eq_left (min_le_left _ _),
        max_eq_right (min_le_right _ _)]
  rw [← he]
  calc
    _ ≤ ‖p nt.1‖*‖p q*a*p q‖*‖p nt.2‖ := norm_mul₃_le
    _ ≤ 1*‖p q*a*p q‖*1 := by gcongr <;> exact (hp.1 _).norm_le _
    _ = _ := by rw [one_mul,mul_one]

end

open Filter Topology
section

inductive BridgeCore (F : Type*)
  | single (i : Bool)
  | double (i : Bool) (a : F) (j : Bool)
  | flank (i : Bool) (a : F) (w : BridgeCore F) (c : F) (j : Bool)

namespace BridgeCore
variable {F B : Type*}
def left : BridgeCore F → Bool
  | .single i | .double i _ _ | .flank i _ _ _ _ => i

def right : BridgeCore F → Bool
  | .single i | .double _ _ i | .flank _ _ _ _ i => !i

def Centered (K : F → Prop) : BridgeCore F → Prop
  | .single _ => True
  | .double _ a _ => K a
  | .flank _ a w c _ => K a ∧ w.Centered K ∧ K c

variable [Monoid B]
def eval (φ : F → B) (b : Bool → B) : BridgeCore F → B
  | .single i => b i
  | .double i a j => b i * φ a * b j
  | .flank i a w c j => b i * φ a * w.eval φ b * φ c * b j

def cons (i : Bool) (a : F) : BridgeCore F → BridgeCore F
  | .single j => .double i a j
  | .double j c k => .flank i a (.single j) c k
  | .flank j c w d k => .flank i a (w.cons j c) d k

theorem eval_cons (φ : F → B) (b : Bool → B) (i : Bool) (a : F) (w : BridgeCore F) :
    (w.cons i a).eval φ b = b i * φ a * w.eval φ b := by
  induction w generalizing i a with
  | single j => rfl
  | double j c k => simp only [cons,eval,mul_assoc]
  | flank j c w d k ih => simp only [cons,eval,ih,mul_assoc]

theorem centered_cons (K : F → Prop) (i : Bool) (a : F) (w : BridgeCore F)
    (ha : K a) (hw : w.Centered K) : (w.cons i a).Centered K := by
  induction w generalizing i a with
  | single j => exact ha
  | double j c k => exact ⟨ha,trivial,hw⟩
  | flank j c w d k ih => exact ⟨ha,ih j c hw.1 hw.2.1,hw.2.2⟩

def snoc (a : F) (j : Bool) : BridgeCore F → BridgeCore F
  | .single i => .double i a j
  | .double i c k => .flank i c (.single k) a j
  | .flank i c w d k => .flank i c (w.snoc d k) a j

theorem eval_snoc (φ : F → B) (b : Bool → B) (a : F) (j : Bool) (w : BridgeCore F) :
    (w.snoc a j).eval φ b = w.eval φ b * φ a * b j := by
  induction w generalizing a j with
  | single i => rfl
  | double i c k => simp only [snoc,eval,mul_assoc]
  | flank i c w d k ih => simp only [snoc,eval,ih,mul_assoc]

theorem centered_snoc (K : F → Prop) (a : F) (j : Bool) (w : BridgeCore F)
    (ha : K a) (hw : w.Centered K) : (w.snoc a j).Centered K := by
  induction w generalizing a j with
  | single i => exact ha
  | double i c k => exact ⟨hw,trivial,ha⟩
  | flank i c w d k ih => exact ⟨hw.1,ih d k hw.2.2 hw.2.1,ha⟩

@[simp] theorem left_cons (i : Bool) (a : F) (w : BridgeCore F) : (w.cons i a).left = i := by
  cases w <;> rfl
@[simp] theorem right_cons (i : Bool) (a : F) (w : BridgeCore F) : (w.cons i a).right = w.right := by
  cases w <;> rfl
@[simp] theorem left_snoc (a : F) (j : Bool) (w : BridgeCore F) : (w.snoc a j).left = w.left := by
  cases w <;> rfl
@[simp] theorem right_snoc (a : F) (j : Bool) (w : BridgeCore F) : (w.snoc a j).right = !j := by
  cases w <;> rfl

variable (φ : F → B) (b e : Bool → B)
  (hleft : ∀ i, e i*b i = b i) (hright : ∀ i, b i*e (!i) = b i)
include hleft in
theorem left_support (w : BridgeCore F) : e w.left*w.eval φ b = w.eval φ b := by
  cases w <;> simp only [left,eval,← mul_assoc,hleft]
include hright in
theorem right_support (w : BridgeCore F) : w.eval φ b*e w.right = w.eval φ b := by
  cases w <;> simp only [right,eval,mul_assoc,hright]
end BridgeCore

variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]
  {i j : I} (hij : i ≠ j) (b : Bool → A j)
  (hb : ∀ v r, (d j).trace (((d j).atom r).1*b v*((d j).atom r).1) = 0)
  (K : A i → Prop)
  (hK : ∀ a, K a → ∀ r, (d i).trace (((d i).atom r).1*a*((d i).atom r).1) = 0)

include hij hb hK

theorem BridgeCore.creation (w : BridgeCore (A i)) (hw : w.Centered K)
    (x : AtomicFockSpace (AtomicLetters d))
    (hx : FockAway (AtomicLetters d) j x) :
    FockStarts (AtomicLetters d) j (w.eval (atomicLeft d i) (fun v => atomicLeft d j (b v)) x) := by
  have hg (v : Bool) (z : AtomicFockSpace (AtomicLetters d))
      (hz : FockAway (AtomicLetters d) j z) :
      FockStarts (AtomicLetters d) j (atomicLeft d j (b v) z) := by
    exact atomicLeft_centered d j (b v) (hb v) z hz
  have hf (a : A i) (ha : K a) (z : AtomicFockSpace (AtomicLetters d))
      (hz : FockStarts (AtomicLetters d) j z) :
      FockAway (AtomicLetters d) j (atomicLeft d i a z) := by
    apply fockStarts_away _ hij
    exact atomicLeft_centered d i a (hK a ha) z (fockStarts_away _ hij.symm _ hz)
  induction w generalizing x with
  | single v => exact hg v x hx
  | double v a u =>
    exact hg v _ (hf a hw _ (hg u x hx))
  | flank v a w c u ih =>
    exact hg v _ (hf a hw.1 _ (ih hw.2.1 _ (hf c hw.2.2 _ (hg u x hx))))

theorem BridgeCore.zero_complement (w : BridgeCore (A i)) (hw : w.Centered K) :
    (1-fockStartProjection (AtomicLetters d) j)*
      w.eval (atomicLeft d i) (fun v => atomicLeft d j (b v))*
      (1-fockStartProjection (AtomicLetters d) j) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change (1-fockStartProjection (AtomicLetters d) j)
    (w.eval (atomicLeft d i) (fun v => atomicLeft d j (b v))
      ((1-fockStartProjection (AtomicLetters d) j) x)) = 0
  rw [sub_apply,one_apply_eq_self,fockStartProjection_fix _ _ _
    (w.creation d hij b hb K hK hw _ (fockStartProjection_complement_away _ _ x)),sub_self]

end

section
variable {F B : Type*} [CStarAlgebra F] [CStarAlgebra B]
  (φ : F →⋆ₐ[ℂ] B) (b : Bool → B) (K : F → Prop)

def bridgeWordSet : Set B := Set.range φ ∪
  {z | ∃ (w : BridgeCore F) (a c : F), w.Centered K ∧ z = φ a*w.eval φ b*φ c}

def bridgeWordSpan : Submodule ℂ B := Submodule.span ℂ (bridgeWordSet φ b K)

theorem bridgeWordSpan_base (a : F) : φ a ∈ bridgeWordSpan φ b K :=
  Submodule.subset_span (Or.inl ⟨a,rfl⟩)

theorem bridgeWordSpan_word (w : BridgeCore F) (a c : F) (hw : w.Centered K) :
    φ a*w.eval φ b*φ c ∈ bridgeWordSpan φ b K :=
  Submodule.subset_span (Or.inr ⟨w,a,c,hw,rfl⟩)

theorem bridgeWordSpan_letter (i : Bool) : b i ∈ bridgeWordSpan φ b K := by
  simpa only [BridgeCore.eval,map_one,one_mul,mul_one] using
    bridgeWordSpan_word φ b K (.single i) 1 1 trivial

theorem bridgeWordSpan_mul_base (a : F) {z : B} (hz : z ∈ bridgeWordSpan φ b K) :
    φ a*z ∈ bridgeWordSpan φ b K := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨c,rfl⟩ | ⟨w,c,d,hw,rfl⟩
    · simpa only [← map_mul] using bridgeWordSpan_base φ b K (a*c)
    · simpa only [map_mul,mul_assoc] using bridgeWordSpan_word φ b K w (a*c) d hw
  | zero => simpa only [mul_zero] using (bridgeWordSpan φ b K).zero_mem
  | add x y hx hy ix iy => simpa only [mul_add] using (bridgeWordSpan φ b K).add_mem ix iy
  | smul c z hz iz => simpa only [mul_smul_comm] using (bridgeWordSpan φ b K).smul_mem c iz

theorem bridgeWordSpan_mul_base_right (a : F) {z : B} (hz : z ∈ bridgeWordSpan φ b K) :
    z*φ a ∈ bridgeWordSpan φ b K := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨c,rfl⟩ | ⟨w,c,d,hw,rfl⟩
    · simpa only [← map_mul] using bridgeWordSpan_base φ b K (c*a)
    · simpa only [map_mul,mul_assoc] using bridgeWordSpan_word φ b K w c (d*a) hw
  | zero => simpa only [zero_mul] using (bridgeWordSpan φ b K).zero_mem
  | add x y hx hy ix iy => simpa only [add_mul] using (bridgeWordSpan φ b K).add_mem ix iy
  | smul c z hz iz => simpa only [smul_mul_assoc] using (bridgeWordSpan φ b K).smul_mem c iz

variable (center : F → F) (hc : ∀ a, K (center a)) (r : Bool → F → Bool → F)
  (hr : ∀ i a j, b i*φ a*b j = b i*φ (center a)*b j + φ (r i a j))
include hc hr

theorem bridgeWordSpan_left_word (i : Bool) (w : BridgeCore F) (a c : F)
    (hw : w.Centered K) : b i*(φ a*w.eval φ b*φ c) ∈ bridgeWordSpan φ b K := by
  have hmain := bridgeWordSpan_word φ b K (w.cons i (center a)) 1 c
    (w.centered_cons K i (center a) (hc a) hw)
  simp only [map_one,one_mul,BridgeCore.eval_cons] at hmain
  cases w with
  | single j =>
    have he : b i*(φ a*b j*φ c) = (b i*φ (center a)*b j*φ c) + φ (r i a j)*φ c := by
      rw [← mul_assoc (b i),← mul_assoc (b i),hr,add_mul]
    rw [BridgeCore.eval,he]
    exact (bridgeWordSpan φ b K).add_mem hmain
      (bridgeWordSpan_mul_base_right φ b K c (bridgeWordSpan_base φ b K _))
  | double j d k =>
    have he : b i*(φ a*(b j*φ d*b k)*φ c) =
        b i*φ (center a)*(b j*φ d*b k)*φ c + φ (r i a j*d)*b k*φ c := by
      calc
        _ = (b i*φ a*b j)*φ d*b k*φ c := by simp only [mul_assoc]
        _ = _ := by rw [hr]; simp only [add_mul,map_mul,mul_assoc]
    rw [BridgeCore.eval,he]
    exact (bridgeWordSpan φ b K).add_mem hmain
      (bridgeWordSpan_word φ b K (.single k) (r i a j*d) c trivial)
  | flank j d w e k =>
    have he : b i*(φ a*(b j*φ d*w.eval φ b*φ e*b k)*φ c) =
        b i*φ (center a)*(b j*φ d*w.eval φ b*φ e*b k)*φ c +
          φ (r i a j*d)*(w.snoc e k).eval φ b*φ c := by
      calc
        _ = (b i*φ a*b j)*φ d*w.eval φ b*φ e*b k*φ c := by simp only [mul_assoc]
        _ = _ := by rw [hr]; simp only [add_mul,map_mul,mul_assoc,BridgeCore.eval_snoc]
    rw [BridgeCore.eval,he]
    exact (bridgeWordSpan φ b K).add_mem hmain
      (bridgeWordSpan_word φ b K (w.snoc e k) (r i a j*d) c
        (w.centered_snoc K e k hw.2.2 hw.2.1))

theorem bridgeWordSpan_mul_letter (i : Bool) {z : B} (hz : z ∈ bridgeWordSpan φ b K) :
    b i*z ∈ bridgeWordSpan φ b K := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨a,rfl⟩ | ⟨w,a,c,hw,rfl⟩
    · simpa only [map_one,one_mul,BridgeCore.eval] using
        bridgeWordSpan_word φ b K (.single i) 1 a trivial
    · exact bridgeWordSpan_left_word φ b K center hc r hr i w a c hw
  | zero => simpa only [mul_zero] using (bridgeWordSpan φ b K).zero_mem
  | add x y hx hy ix iy => simpa only [mul_add] using (bridgeWordSpan φ b K).add_mem ix iy
  | smul c z hz iz => simpa only [mul_smul_comm] using (bridgeWordSpan φ b K).smul_mem c iz

theorem adjoin_le_bridgeWordSpan :
    (Algebra.adjoin ℂ (Set.range φ ∪ Set.range b)).toSubmodule ≤ bridgeWordSpan φ b K := by
  intro z hz
  have hinv : ∀ x ∈ Algebra.adjoin ℂ (Set.range φ ∪ Set.range b),
      ∀ y ∈ bridgeWordSpan φ b K, x*y ∈ bridgeWordSpan φ b K := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨a,rfl⟩ | ⟨i,rfl⟩
      · exact fun y hy => bridgeWordSpan_mul_base φ b K a hy
      · exact fun y hy => bridgeWordSpan_mul_letter φ b K center hc r hr i hy
    | algebraMap s =>
      intro y hy
      simpa only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul] using
        (bridgeWordSpan φ b K).smul_mem s hy
    | add x y hx hy ix iy =>
      intro z hz
      simpa only [add_mul] using (bridgeWordSpan φ b K).add_mem (ix z hz) (iy z hz)
    | mul x y hx hy ix iy =>
      intro z hz
      simpa only [mul_assoc] using ix (y*z) (iy z hz)
  have h1 : (1:B) ∈ bridgeWordSpan φ b K := by
    simpa only [map_one] using bridgeWordSpan_base φ b K 1
  simpa only [mul_one] using hinv z hz 1 h1

end

section
open scoped CStarAlgebra
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
  [PartialOrder A] [StarOrderedRing A]
  [PartialOrder D] [StarOrderedRing D]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)
  (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
  (δ : Bool → D →⋆ₐ[ℂ] A)
  (hd : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x))

def bridgeLetter (i : Bool) : Z := ψ (matrixSingle i (!i) (1:D))

def bridgeSupport (i : Bool) : Z := φ (matrixSingle i i (1:A))

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem bridgeLetter_support_left (i : Bool) :
    bridgeSupport φ i * bridgeLetter ψ i = bridgeLetter ψ i := by
  rw [bridgeSupport,matrixDiagonal_units φ ψ δ hd,bridgeLetter,← map_mul,
    matrixSingle_mul,one_mul]

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem bridgeLetter_support_right (i : Bool) :
    bridgeLetter ψ i * bridgeSupport φ (!i) = bridgeLetter ψ i := by
  rw [bridgeSupport,matrixDiagonal_units φ ψ δ hd,bridgeLetter,← map_mul,
    matrixSingle_mul,mul_one]

theorem bridgeSupport_norm (i : Bool) : ‖bridgeSupport φ i‖ ≤ 1 :=
  (NonUnitalStarAlgHom.norm_apply_le _ _).trans
    ((matrixSingle_projection i (1:A) (by constructor <;> simp [IsIdempotentElem,IsSelfAdjoint])).norm_le _)

omit [PartialOrder D] [StarOrderedRing D] in
@[simp] theorem bridgeLetter_star (i : Bool) : star (bridgeLetter ψ i) = bridgeLetter ψ (!i) := by
  simp only [bridgeLetter,← map_star,matrixSingle_star,star_one,Bool.not_not]

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in

theorem bridgeLetter_transfer (g : D) (i : Bool) :
    φ (matrixSingle i i (δ i g))*bridgeLetter ψ i =
      bridgeLetter ψ i*φ (matrixSingle (!i) (!i) (δ (!i) g)) := by
  rw [matrixDiagonal_agrees φ ψ δ hd,matrixDiagonal_agrees φ ψ δ hd,
    bridgeLetter,← map_mul,← map_mul,matrixSingle_mul,matrixSingle_mul,mul_one,one_mul]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem matrixSingle_diagonal_general (x : Bool → D) (i j : Bool) (a : A) :
    matrixSingle i j a * matrixDiagonalHom δ x = matrixSingle i j (a * δ j (x j)) := by
  ext k l
  change (Matrix.single i j a * Matrix.diagonal (fun v => δ v (x v))) k l = _
  rw [Matrix.mul_diagonal]
  by_cases h : i = k ∧ j = l
  · rcases h with ⟨rfl,rfl⟩; simp
  · simp [matrixSingle_apply,h]

omit [PartialOrder D] [StarOrderedRing D] in

theorem matrix_offdiagonal_turn (x : Bool → D) (i j : Bool) :
    matrixSingle i (!i) (1:D) * matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x *
      matrixSingle j (!j) 1 =
    matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D)
      (Pi.single i (if j = !i then x (!i) else 0)) := by
  rw [matrixSingle_diagonal_general]
  simp only [StarAlgHom.coe_id, id_eq, one_mul]
  by_cases h : j = !i
  · subst j
    rw [ite_eq_left rfl,matrixSingle_mul,Bool.not_not,mul_one,matrixDiagonalHom_single]
    rfl
  · rw [matrixSingle_mul_of_ne _ _ _ _ _ _ (Ne.symm h),ite_eq_right h,Pi.single_zero,map_zero]

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in

theorem bridgeLetter_diagonal_turn (x : Bool → D) (i j : Bool) :
    bridgeLetter ψ i * φ (matrixDiagonalHom δ x) * bridgeLetter ψ j =
      φ (matrixDiagonalHom δ (Pi.single i (if j = !i then x (!i) else 0))) := by
  rw [hd,bridgeLetter,bridgeLetter,← map_mul,← map_mul,matrix_offdiagonal_turn,← hd]

variable (E : CStarMatrix Bool Bool A →L[ℂ] (Bool → D))
  (hE : ∀ x, E (matrixDiagonalHom δ x) = x)

def bridgeCenter (a : CStarMatrix Bool Bool A) : CStarMatrix Bool Bool A :=
  a - matrixDiagonalHom δ (E a)

include hE in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem bridgeCenter_centered (a : CStarMatrix Bool Bool A) : E (bridgeCenter δ E a) = 0 := by
  rw [bridgeCenter,map_sub,hE,sub_self]

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem bridgeLetter_turn (i : Bool) (a : CStarMatrix Bool Bool A) (j : Bool) :
    bridgeLetter ψ i * φ a * bridgeLetter ψ j =
      bridgeLetter ψ i * φ (bridgeCenter δ E a) * bridgeLetter ψ j +
        φ (matrixDiagonalHom δ (Pi.single i (if j = !i then (E a) (!i) else 0))) := by
  rw [bridgeCenter,map_sub,mul_sub,sub_mul,bridgeLetter_diagonal_turn φ ψ δ hd]
  exact (sub_add_cancel _ _).symm

include hd hE in
omit [PartialOrder D] [StarOrderedRing D] in

theorem matrix_bridge_adjoin_le_span :
    (Algebra.adjoin ℂ (Set.range φ ∪ Set.range (bridgeLetter ψ))).toSubmodule ≤
      bridgeWordSpan φ (bridgeLetter ψ) (fun a => E a = 0) := by
  exact adjoin_le_bridgeWordSpan φ (bridgeLetter ψ) (fun a => E a = 0)
    (bridgeCenter δ E) (bridgeCenter_centered δ E hE)
    (fun i a j => matrixDiagonalHom δ (Pi.single i (if j = !i then (E a) (!i) else 0)))
    (bridgeLetter_turn φ ψ δ hd E)

end

section
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  {d : ∀ i, AtomicTraceData (A i) V} [DecidableEq I] [DecidableEq V]
  {Δ : Type*} [CStarAlgebra Δ] (c : AtomicAmalgamData (Δ := Δ) d)

theorem AtomicAmalgamData.left_agree (i j : I) (x : Δ) :
    atomicLeft d i (c.diagonal i x) = atomicLeft d j (c.diagonal j x) :=
  atomicLeft_diagonal_agree d c.diagonal c.coordinate c.atom_mul i j x

omit [DecidableEq V] in

theorem AtomicAmalgamData.core_zero {i j : I} (hij : i ≠ j) (b : Bool → A j)
    (hb : ∀ k, c.expectation j (b k) = 0)
    (w : BridgeCore (A i)) (hw : w.Centered (fun a => c.expectation i a = 0)) :
    (1-fockStartProjection (AtomicLetters d) j)*
      w.eval (atomicLeft d i) (fun k => atomicLeft d j (b k))*
      (1-fockStartProjection (AtomicLetters d) j) = 0 :=
  w.zero_complement d hij b (fun k => c.centered j _ (hb k))
    (fun a => c.expectation i a = 0) (fun a ha => c.centered i a ha) hw
end

open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra
section
variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
  (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)

theorem peakingCoefficients_peak_nat (m n : ℕ) :
    peakingCoefficients hp τ hτ hpos (p n) m = if m < n then 0 else 1 := by
  rw [peakingCoefficients_nat]
  by_cases h : m < n
  · rw [ite_eq_left h,cornerState_apply,hp.peakAtom_mul_peak h,zero_mul,map_zero,smul_zero]
  · rw [ite_eq_right h]
    exact cornerState_eq_one τ hτ _ _ (hp.peakAtom_projection m) (hp.1 n)
      ((hp.peakAtom_le m).trans (hp.2.1 (Nat.le_of_not_gt h))) (hpos m)

theorem peakingCoefficients_peak_eq
    {q : ℕ → B} {g : B →L[ℂ] ℂ} (hq : Peaks q g)
    (σ : B →L[ℂ] ℂ) (hσ : IsState σ) (hposq : ∀ n, 0 < (σ (peakAtom q n)).re) (n : ℕ) :
    peakingCoefficients hp τ hτ hpos (p n) = peakingCoefficients hq σ hσ hposq (q n) := by
  ext x
  induction x using OnePoint.rec with
  | infty => rw [peakingCoefficients_infty,peakingCoefficients_infty,hp.2.2.2.1,hq.2.2.2.1]
  | coe m => rw [peakingCoefficients_peak_nat,peakingCoefficients_peak_nat]

include τ hτ hpos in

theorem sequenceDiagonalHom_matched_peak (hp0 : p 0 = 1)
    (d : AtomicTraceData A ℕ) (hd : ∀ m, (d.atom m).1 = peakAtom p m)
    {q : ℕ → B} {g : B →L[ℂ] ℂ} (hq : Peaks q g)
    (σ : B →L[ℂ] ℂ) (hσ : IsState σ) (hposq : ∀ m, 0 < (σ (peakAtom q m)).re) (n : ℕ) :
    sequenceDiagonalHom hp d hd (peakingCoefficients hq σ hσ hposq (q n)) = p n := by
  rw [← peakingCoefficients_peak_eq hp τ hτ hpos hq σ hσ hposq n,
    sequenceDiagonalHom_peakingCoefficients hp hp0,peakingExpectation_peak hp hp0]

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

structure PeakingPairData (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  trace : A →ₚ[ℂ] ℂ
  tracial : IsTracialPositive trace
  normalized : trace 1 = 1
  faithful : ∀ a, trace (star a*a) = 0 → a = 0
  peak : Bool → ℕ → A
  state : Bool → A →L[ℂ] ℂ
  peaks : ∀ i, Peaks (peak i) (state i)
  peak_zero : ∀ i, peak i 0 = 1
  atom_positive : ∀ i v, 0 < (trace (peakAtom (peak i) v)).re
  trace_null : ∀ i, Tendsto (fun v => (trace (peak i v)).re) atTop (𝓝 0)
  matched : ∀ i v, trace (peak i v) = trace (peak false v)

namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

local instance matrixFamilyStarOrder : (j : Bool) →
    StarOrderedRing (CStarMatrix Bool Bool (HNNFactor A j)) := fun _ => inferInstance

def input : (j : Bool) → MatrixDiagonalInput (n := Bool) (HNNFactor A j)
    (fun x : SequenceDiagonal => fun v : ℕ => x v) := hnnMatrixInput B.trace B.tracial B.normalized B.faithful B.peak B.state
  B.peaks B.peak_zero B.atom_positive B.trace_null

def atoms : (j : Bool) → AtomicTraceData (CStarMatrix Bool Bool (HNNFactor A j)) (Bool × ℕ) := matrixInputData (fun x : SequenceDiagonal => fun v : ℕ => x v) B.input

def amalgam : AtomicAmalgamData (Δ := Bool → SequenceDiagonal) B.atoms := hnnAmalgamData B.trace B.tracial B.normalized B.faithful B.peak B.state
  B.peaks B.peak_zero B.atom_positive B.trace_null B.matched

abbrev Model := AtomicCStar B.atoms

instance modelCStarAlgebra : CStarAlgebra B.Model := inferInstance

instance modelAddZeroClass : AddZeroClass B.Model :=
  B.modelCStarAlgebra.toAddZeroClass

abbrev Operators := AtomicOperators B.atoms
abbrev base := atomicLeft B.atoms false
abbrev aux := atomicLeft B.atoms true
abbrev diagonal := (B.input false).diagonal
abbrev expectation := B.amalgam.expectation false

theorem amalgam_diagonal_false : B.amalgam.diagonal false = matrixDiagonalHom B.diagonal := rfl

theorem amalgam_diagonal_true : B.amalgam.diagonal true =
    matrixDiagonalHom (fun _ => StarAlgHom.id ℂ SequenceDiagonal) := rfl

theorem diagonal_agree (x : Bool → SequenceDiagonal) :
    B.base (matrixDiagonalHom B.diagonal x) =
      B.aux (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ SequenceDiagonal) x) :=
by
  rw [← B.amalgam_diagonal_false, ← B.amalgam_diagonal_true]
  unfold base aux
  exact B.amalgam.left_agree false true x

theorem expectation_eq : B.expectation =
    matrixPeakingExpectation B.peaks (positiveCLM B.trace)
      (positiveCLM_isState B.trace B.normalized) B.atom_positive := rfl

theorem expectation_fixes (x : Bool → SequenceDiagonal) :
    B.expectation (matrixDiagonalHom B.diagonal x) = x := B.amalgam.fix false x

theorem letter_centered (i : Bool) :
    B.amalgam.expectation true (matrixSingle i (!i) (1:SequenceDiagonal)) = 0 := by
  ext j x
  change (matrixDiagonalExpectation (B.input true).expectation (B.input true).bound
    (matrixSingle i (!i) (1:SequenceDiagonal))) j x = 0
  rw [matrixDiagonalExpectation_apply]
  have hn : ¬ (i = j ∧ (!i) = j) := by cases i <;> cases j <;> simp
  rw [matrixSingle_apply,ite_eq_right hn,map_zero]
  rfl

abbrev letter := bridgeLetter B.aux
abbrev support := bridgeSupport B.base
abbrev start := fockStartProjection (AtomicLetters B.atoms) true

theorem core_zero (w : BridgeCore (CStarMatrix Bool Bool A))
    (hw : w.Centered (fun a => B.expectation a = 0)) :
    (1-B.start)*w.eval B.base B.letter*(1-B.start) = 0 := by
  unfold start letter base aux bridgeLetter
  exact B.amalgam.core_zero (by decide : false ≠ true)
      (fun i => matrixSingle i (!i) (1:SequenceDiagonal)) B.letter_centered w hw

def tail (n : ℕ) : SequenceDiagonal :=
  peakingCoefficients (B.peaks false) (positiveCLM B.trace)
    (positiveCLM_isState B.trace B.normalized) (B.atom_positive false) (B.peak false n)

theorem diagonal_tail (i : Bool) (n : ℕ) : B.diagonal i (B.tail n) = B.peak i n := by
  exact sequenceDiagonalHom_matched_peak (B.peaks i) (positiveCLM B.trace)
    (positiveCLM_isState B.trace B.normalized) (B.atom_positive i) (B.peak_zero i)
    (peakAtomicTraceData (B.peaks i) (B.peak_zero i) B.trace B.tracial B.normalized
      B.faithful (B.atom_positive i) (B.trace_null i)) (fun _ => rfl)
    (B.peaks false) (positiveCLM B.trace) (positiveCLM_isState B.trace B.normalized)
    (B.atom_positive false) n

def matrixPeak (i : Bool) (n : ℕ) : CStarMatrix Bool Bool A := matrixSingle i i (B.peak i n)

theorem peak_transfer (i : Bool) (n : ℕ) :
    B.base (B.matrixPeak i n)*B.letter i = B.letter i*B.base (B.matrixPeak (!i) n) := by
  simpa only [B.diagonal_tail,matrixPeak] using
    bridgeLetter_transfer B.base B.aux B.diagonal B.diagonal_agree (B.tail n) i

end PeakingPairData

section
open scoped CStarAlgebra
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)
  (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
  (δ : Bool → D →⋆ₐ[ℂ] A)
  (hd : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x))

omit [PartialOrder D] [StarOrderedRing D] in
theorem matrix_eq_sum_entries (M : CStarMatrix Bool Bool D) :
    M = ∑ i : Bool, ∑ j : Bool, matrixSingle i j (M i j) := by
  change CStarMatrix.ofMatrix.symm M = ∑ i : Bool, ∑ j : Bool, Matrix.single i j (M i j)
  exact Matrix.matrix_eq_sum_single _

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in

theorem matrixAux_mem_adjoin (M : CStarMatrix Bool Bool D) :
    ψ M ∈ Algebra.adjoin ℂ (Set.range φ ∪ Set.range (bridgeLetter ψ)) := by
  let S := Algebra.adjoin ℂ (Set.range φ ∪ Set.range (bridgeLetter ψ))
  have hdiag (i : Bool) (a : D) : ψ (matrixSingle i i a) ∈ S := by
    rw [← matrixDiagonal_agrees φ ψ δ hd]
    exact Algebra.subset_adjoin (Or.inl ⟨_,rfl⟩)
  have hoff (i : Bool) (a : D) : ψ (matrixSingle i (!i) a) ∈ S := by
    have he : ψ (matrixSingle i (!i) a) =
        ψ (matrixSingle i i a)*bridgeLetter ψ i := by
      rw [bridgeLetter,← map_mul,matrixSingle_mul,mul_one]
    rw [he]
    exact S.mul_mem (hdiag i a) (Algebra.subset_adjoin (Or.inr ⟨i,rfl⟩))
  rw [matrix_eq_sum_entries M,map_sum]
  apply S.sum_mem
  intro i _
  rw [map_sum]
  apply S.sum_mem
  intro j _
  by_cases h : j = i
  · subst j; exact hdiag i _
  · have he : j = !i := by cases i <;> cases j <;> simp_all
    subst j
    exact hoff i _

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem matrix_bridge_generators :
    Algebra.adjoin ℂ (Set.range φ ∪ Set.range ψ) =
      Algebra.adjoin ℂ (Set.range φ ∪ Set.range (bridgeLetter ψ)) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x (⟨a,rfl⟩ | ⟨a,rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨a,rfl⟩)
    · exact matrixAux_mem_adjoin φ ψ δ hd a
  · apply Algebra.adjoin_le
    rintro x (⟨a,rfl⟩ | ⟨i,rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨a,rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨matrixSingle i (!i) 1,rfl⟩)

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

local instance modelPartialOrder : PartialOrder B.Model := CStarAlgebra.spectralOrder _
local instance modelStarOrderedRing : StarOrderedRing B.Model := CStarAlgebra.spectralOrderedRing _

abbrev embedBase := atomicEmbedding B.atoms false
abbrev embedAux := atomicEmbedding B.atoms true
abbrev modelLetter := bridgeLetter B.embedAux

@[simp] theorem coe_embedBase (a : CStarMatrix Bool Bool A) :
    (B.embedBase a : B.Operators) = B.base a := rfl

@[simp] theorem coe_embedAux (a : CStarMatrix Bool Bool SequenceDiagonal) :
    (B.embedAux a : B.Operators) = B.aux a := rfl

@[simp] theorem coe_modelLetter (i : Bool) :
    (B.modelLetter i : B.Operators) = B.letter i := rfl

theorem model_diagonal_agree (x : Bool → SequenceDiagonal) :
    B.embedBase (matrixDiagonalHom B.diagonal x) =
      B.embedAux (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ SequenceDiagonal) x) := by
  apply Subtype.ext
  exact B.diagonal_agree x

theorem model_factors_dense :
    Dense (Algebra.adjoin ℂ (Set.range B.embedBase ∪ Set.range B.embedAux) : Set B.Model) := by
  let S : Subalgebra ℂ B.Model := Algebra.adjoin ℂ (Set.range B.embedBase ∪ Set.range B.embedAux)
  have hlift (a : B.Operators) (ha : a ∈ atomicAlgebra B.atoms) :
      (⟨a,subset_closure ha⟩ : B.Model) ∈ S := by
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases Set.mem_iUnion.mp ha with ⟨i,hi⟩
      rcases hi with ⟨b,rfl⟩
      apply Algebra.subset_adjoin
      cases i with
      | false => exact Or.inl ⟨b,rfl⟩
      | true => exact Or.inr ⟨b,rfl⟩
    | algebraMap c => exact S.algebraMap_mem c
    | add a b _ _ ha hb => exact S.add_mem ha hb
    | mul a b _ _ ha hb => exact S.mul_mem ha hb
  have hd : DenseRange (fun a : atomicAlgebra B.atoms =>
      (⟨a.1,subset_closure a.2⟩ : B.Model)) :=
    (denseRange_inclusion_iff subset_closure).mpr Set.Subset.rfl
  exact hd.mono (by rintro a ⟨a,rfl⟩; exact hlift a.1 a.2)

theorem model_words_dense :
    Dense (bridgeWordSpan B.embedBase B.modelLetter (fun a => B.expectation a = 0) : Set B.Model) := by
  have hd := B.model_factors_dense
  rw [matrix_bridge_generators B.embedBase B.embedAux B.diagonal B.model_diagonal_agree] at hd
  exact hd.mono (matrix_bridge_adjoin_le_span B.embedBase B.embedAux B.diagonal
    B.model_diagonal_agree B.expectation B.expectation_fixes)

theorem coe_core (w : BridgeCore (CStarMatrix Bool Bool A)) :
    (↑(w.eval B.embedBase B.modelLetter : B.Model) : B.Operators) = w.eval B.base B.letter := by
  induction w with
  | single i => rfl
  | double i a j => rfl
  | flank i a w c j ih =>
    change B.letter i*B.base a*(↑(w.eval B.embedBase B.modelLetter : B.Model) : B.Operators)*B.base c*B.letter j = _
    rw [ih]
    rfl

end PeakingPairData

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
section
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n]

theorem matrixState_isPureState (f : A →L[ℂ] ℂ) (hf : IsPureState f) (i : n) :
    IsPureState (matrixState f i) := by
  rw [IsPureState, mem_extremePoints]
  refine ⟨matrixState_isState f hf.1 i, ?_⟩
  intro g hg h hh hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  have hface := state_projection_face g h hg hh (matrixSingle i i (1:A))
    (matrixSingle_projection i 1 (by constructor <;> simp [IsIdempotentElem,IsSelfAdjoint]))
    a b ha hb hab (by rw [heq]; simp [((isState_iff f).mp hf.1).1])
  have hgc := matrix_corner_isState g hg i hface.1
  have hhc := matrix_corner_isState h hh i hface.2
  have heqc : a • (g.comp (matrixSingleCLM i)) + b • (h.comp (matrixSingleCLM i)) = f := by
    ext x
    have he := congrArg (fun k : CStarMatrix n n A →L[ℂ] ℂ => k (matrixSingle i i x)) heq
    change a • g (matrixSingle i i x) + b • h (matrixSingle i i x) = f x
    simpa using he
  have hbase := (mem_extremePoints.mp hf).2 _ hgc _ hhc ⟨a,b,ha,hb,hab,heqc⟩
  constructor
  · ext M
    rw [matrix_state_supported g hg i hface.1 M,matrixState_apply]
    exact congrArg (fun k : A →L[ℂ] ℂ => k (M i i)) hbase.1
  · ext M
    rw [matrix_state_supported h hh i hface.2 M,matrixState_apply]
    exact congrArg (fun k : A →L[ℂ] ℂ => k (M i i)) hbase.2

omit [PartialOrder A] [StarOrderedRing A] in

theorem matrix_conjugate_entry (M : CStarMatrix n n A) (i j : n) (a : A) :
    (star M * matrixSingle j j a * M) i i = star (M j i)*a*M j i := by
  change ((CStarMatrix.ofMatrix.symm M).conjTranspose * Matrix.single j j a *
    CStarMatrix.ofMatrix.symm M) i i = _
  simp [Matrix.mul_apply,Matrix.single,Matrix.conjTranspose_apply,ite_and]

theorem matrix_pure_equivalence_reflects (f g : A →L[ℂ] ℂ)
    (hf : IsPureState f) (hg : IsPureState g) (i j : n)
    (he : UnitarilyEquivalent
      (pureGNS (matrixState f i) (matrixState_isPureState f hf i))
      (pureGNS (matrixState g j) (matrixState_isPureState g hg j))) :
    UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg) := by
  let F := positiveOfSquares (matrixState f i) (matrixState_isState f hf.1 i).2
  let G := positiveOfSquares (matrixState g j) (matrixState_isState g hg.1 j).2
  have hFn : ‖gnsVector F‖ = 1 := gnsVector_norm_eq_one F
    ((isState_iff _).mp (matrixState_isState f hf.1 i)).1
  have hGn : ‖gnsVector G‖ = 1 := gnsVector_norm_eq_one G
    ((isState_iff _).mp (matrixState_isState g hg.1 j)).1
  obtain ⟨u,hu⟩ := equivalent_vector_states_unitary F.gnsNonUnitalStarAlgHom
    (pure_gns_irreducible _ (matrixState_isState f hf.1 i) (matrixState_isPureState f hf i))
    G.gnsNonUnitalStarAlgHom he (gnsVector F) (gnsVector G) hFn hGn
  have hFc (a : CStarMatrix n n A) :
      ⟪gnsVector F,F.gnsNonUnitalStarAlgHom a (gnsVector F)⟫_ℂ = matrixState f i a :=
    gnsVector_coefficient F a
  have hGc (a : CStarMatrix n n A) :
      ⟪gnsVector G,G.gnsNonUnitalStarAlgHom a (gnsVector G)⟫_ℂ = matrixState g j a :=
    gnsVector_coefficient G a
  have hc (a : A) : g a = f (star ((u : CStarMatrix n n A) j i)*a*(u : CStarMatrix n n A) j i) := by
    have hh := hu (matrixSingle j j a)
    simpa only [hFc,hGc,matrixState_apply,
      matrixSingle_apply,ite_true,and_self,matrix_conjugate_entry] using hh
  let f₀ := positiveOfSquares f hf.1.2
  let g₀ := positiveOfSquares g hg.1.2
  let π := f₀.gnsNonUnitalStarAlgHom
  let ρ := g₀.gnsNonUnitalStarAlgHom
  let ξ := gnsVector f₀
  let η := gnsVector g₀
  let v : A := (u : CStarMatrix n n A) j i
  have hcoeff (a : A) : ⟪π v ξ,π a (π v ξ)⟫_ℂ = ⟪η,ρ a η⟫_ℂ := by
    calc
      _ = f (star v*a*v) := by
        have he : ⟪ξ,π (star v*a*v) ξ⟫_ℂ = f (star v*a*v) :=
          gnsVector_coefficient f₀ _
        rw [map_mul,map_mul,map_star,mul_apply_eq_comp,mul_apply_eq_comp,
          ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at he
        exact he
      _ = _ := (hc a).symm.trans (gnsVector_coefficient g₀ a).symm
  have hη : η ≠ 0 := by
    have hn := gnsVector_norm_eq_one g₀ ((isState_iff g).mp hg.1).1
    exact norm_ne_zero_iff.mp (hn.trans_ne one_ne_zero)
  have hξ : π v ξ ≠ 0 := by
    intro hz
    have hh := hcoeff 1
    rw [hz,inner_zero_left] at hh
    exact zero_ne_one ((hh.trans (gnsVector_coefficient g₀ 1)).trans ((isState_iff g).mp hg.1).1)
  exact irreducible_equivalent_of_coefficients π (pure_gns_irreducible f hf.1 hf)
    ρ (pure_gns_irreducible g hg.1 hg) (π v ξ) η hξ hη hcoeff

end

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {ι κ : Type*} [Preorder ι] [Preorder κ]
  [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]

theorem state_cross_excision (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (x : ι → A) (y : κ → A)
    (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1)
    (hy : ∀ j, 0 ≤ y j) (hyn : ∀ j, ‖y j‖ ≤ 1) (hym : Antitone y)
    (hexc : ∀ a, Tendsto (fun i => x i*(a-f a • (1:A))*x i) atTop (𝓝 0))
    (hey : ∀ a, Tendsto (fun j => y j*(a-g a • (1:A))*y j) atTop (𝓝 0))
    (hne : ¬ UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg)) (a : A) :
    Tendsto (fun ij : ι × κ => x ij.1*a*y ij.2) atTop (𝓝 0) := by
  apply cross_excision_tendsto x y f hx hxn hy hyn hym hexc a
  let F := positiveOfSquares f hf.1.2
  let G := positiveOfSquares g hg.1.2
  have hfcoef (b : A) : ⟪gnsVector F,F.gnsNonUnitalStarAlgHom b (gnsVector F)⟫_ℂ = f b :=
    gnsVector_coefficient F b
  have hgcoef (b : A) : ⟪gnsVector G,G.gnsNonUnitalStarAlgHom b (gnsVector G)⟫_ℂ = g b :=
    gnsVector_coefficient G b
  have ht := excision_inequivalent_strong G.gnsNonUnitalStarAlgHom
    (pure_gns_irreducible g hg.1 hg) (gnsVector G)
    (gnsVector_norm_eq_one G ((isState_iff g).mp hg.1).1) y hy hyn
    (fun b => by simpa only [hgcoef] using hey b)
    F.gnsNonUnitalStarAlgHom (pure_gns_irreducible f hf.1 hf)
    (fun h => hne h.symm) (F.gnsNonUnitalStarAlgHom (star a) (gnsVector F))
  simpa only [star_star,hfcoef] using
    vector_sandwich_tendsto F.gnsNonUnitalStarAlgHom (gnsVector F) y (star a) ht

end

open Filter Topology
section
variable {F B γ : Type*} [CStarAlgebra F] [CStarAlgebra B] {l : Filter γ}
  (φ : F →⋆ₐ[ℂ] B) (b e : Bool → B) (P : B) (hP : IsStarProjection P)
  (hel : ∀ i, e i*b i = b i) (her : ∀ i, b i*e (!i) = b i)
  (hen : ∀ i, ‖e i‖ ≤ 1) (K : F → Prop)
  (hz : ∀ w : BridgeCore F, w.Centered K → (1-P)*w.eval φ b*(1-P) = 0)
include hel her hen hz hP

theorem supported_core_decay (w : BridgeCore F) (hw : w.Centered K)
    (x y : γ → B) (hx : ∀ k, ‖x k‖ ≤ 1) (hy : ∀ k, ‖y k‖ ≤ 1) (a c : F)
    (hl : Tendsto (fun k => x k*φ a*e w.left*P) l (𝓝 0))
    (hr : Tendsto (fun k => P*(e w.right*φ c*y k)) l (𝓝 0)) :
    Tendsto (fun k => x k*φ a*w.eval φ b*φ c*y k) l (𝓝 0) := by
  have hd (k : γ) : ‖x k*φ a*e w.left‖ ≤ ‖φ a‖ := by
    calc
      _ ≤ ‖x k‖*‖φ a‖*‖e w.left‖ := norm_mul₃_le
      _ ≤ 1*‖φ a‖*1 := by gcongr <;> first | exact hx k | exact hen _
      _ = _ := by rw [one_mul,mul_one]
  have he (k : γ) : ‖e w.right*φ c*y k‖ ≤ ‖φ c‖ := by
    calc
      _ ≤ ‖e w.right‖*‖φ c‖*‖y k‖ := norm_mul₃_le
      _ ≤ 1*‖φ c‖*1 := by gcongr <;> first | exact hy k | exact hen _
      _ = _ := by rw [one_mul,mul_one]
  have ht := two_end_tendsto P (w.eval φ b) hP (hz w hw)
    (fun k => x k*φ a*e w.left) (fun k => e w.right*φ c*y k)
    ‖φ a‖ ‖φ c‖ hd he hl hr
  have hid (k : γ) : (x k*φ a*e w.left)*w.eval φ b*(e w.right*φ c*y k) =
      x k*φ a*w.eval φ b*φ c*y k := by
    calc
      _ = x k*φ a*(e w.left*w.eval φ b*e w.right)*φ c*y k := by simp only [mul_assoc]
      _ = _ := by rw [w.left_support φ b e hel,w.right_support φ b e her]
  simpa only [hid] using ht

omit hel her hen hz hP

def bridgeZeroPart (f : Bool → F →L[ℂ] ℂ) (tag : Option Bool) (i : Bool) (a : F) : F :=
  if tag = some i then a-f i a • 1 else a

def bridgeScalarPart (f : Bool → F →L[ℂ] ℂ) (tag : Option Bool) (i : Bool) (a : F) : ℂ :=
  if tag = some i then f i a else 0

theorem bridge_split (f : Bool → F →L[ℂ] ℂ) (tag : Option Bool) (i : Bool) (a : F) :
    a = bridgeZeroPart f tag i a + bridgeScalarPart f tag i a • 1 := by
  by_cases h : tag = some i <;> simp [bridgeZeroPart,bridgeScalarPart,h]

theorem bridgeZeroPart_good (f : Bool → F →L[ℂ] ℂ) (hf : ∀ i, f i 1 = 1)
    (tag : Option Bool) (i : Bool) (a : F) :
    tag ≠ some i ∨ f i (bridgeZeroPart f tag i a) = 0 := by
  by_cases h : tag = some i
  · right
    simp [bridgeZeroPart,h,map_sub,map_smul,hf]
  · exact Or.inl h

theorem bridge_four_terms (a c : F) (a' c' : F) (α β : ℂ)
    (ha : a = a'+α • 1) (hc : c = c'+β • 1) (x y w : B) :
    x*φ a*w*φ c*y = (x*φ a'*w*φ c'*y + α • (x*w*φ c'*y)) +
      (β • (x*φ a'*w*y) + (α*β) • (x*w*y)) := by
  rw [ha,hc]
  simp only [map_add,map_smul,map_one,mul_add,add_mul,mul_smul_comm,
    smul_mul_assoc,mul_one,smul_add,smul_smul,mul_comm β α]

structure BridgeDecayData (f : Bool → F →L[ℂ] ℂ) (x y : γ → B)
    (px py : Bool → γ → B) (tx ty : Option Bool) : Prop where
  normX : ∀ k, ‖x k‖ ≤ 1
  normY : ∀ k, ‖y k‖ ≤ 1
  normPX : ∀ i k, ‖px i k‖ ≤ 1
  normPY : ∀ i k, ‖py i k‖ ≤ 1
  normState : ∀ i, f i 1 = 1
  matchedX : ∀ i, tx = some i → ∀ k, x k = px i k
  matchedY : ∀ i, ty = some i → ∀ k, y k = py i k
  transferX : ∀ i k, px i k*b i = b i*px (!i) k
  transferY : ∀ i k, b i*py (!i) k = py i k*b i
  exclude : ∀ i, tx = some i → ty ≠ some (!i)
  cutX : ∀ i a, (tx ≠ some i ∨ f i a = 0) →
    Tendsto (fun k => x k*φ a*e i*P) l (𝓝 0)
  cutY : ∀ i a, (ty ≠ some i ∨ f i a = 0) →
    Tendsto (fun k => P*(e i*φ a*y k)) l (𝓝 0)
  cutPX : ∀ j i a, K a → Tendsto (fun k => px j k*φ a*e i*P) l (𝓝 0)
  cutPY : ∀ j i a, K a → Tendsto (fun k => P*(e i*φ a*py j k)) l (𝓝 0)
  crossX : ∀ i a, tx = some i → ty ≠ some (!i) →
    Tendsto (fun k => px (!i) k*φ a*y k) l (𝓝 0)
  crossY : ∀ i a, ty = some (!i) → tx ≠ some i →
    Tendsto (fun k => x k*φ a*py i k) l (𝓝 0)
  rectangle : ∀ i a, K a → Tendsto (fun k => px i k*φ a*py i k) l (𝓝 0)

variable {f : Bool → F →L[ℂ] ℂ} {x y : γ → B} {px py : Bool → γ → B} {tx ty : Option Bool}
  (D : BridgeDecayData φ b e P K (l := l) f x y px py tx ty)
include hel her hen hz hP D

theorem bridge_left_transfer (i : Bool) (hi : tx = some i)
    (w : BridgeCore F) (hw : w.Centered K) (a c : F) (ha : K a)
    (hc : ty ≠ some w.right ∨ f w.right c = 0) :
    Tendsto (fun k => x k*b i*φ a*w.eval φ b*φ c*y k) l (𝓝 0) := by
  have ht := supported_core_decay φ b e P hP hel her hen K hz w hw
    (px (!i)) y (D.normPX _) D.normY a c (D.cutPX _ _ _ ha) (D.cutY _ _ hc)
  have he (k : γ) : x k*b i*φ a*w.eval φ b*φ c*y k =
      b i*(px (!i) k*φ a*w.eval φ b*φ c*y k) := by
    rw [D.matchedX i hi k,D.transferX]
    simp only [mul_assoc]
  simpa only [he,mul_zero] using tendsto_const_nhds.mul ht

theorem bridge_right_transfer (j : Bool) (hj : ty = some (!j))
    (w : BridgeCore F) (hw : w.Centered K) (a c : F) (hc : K c)
    (ha : tx ≠ some w.left ∨ f w.left a = 0) :
    Tendsto (fun k => x k*φ a*w.eval φ b*φ c*b j*y k) l (𝓝 0) := by
  have ht := supported_core_decay φ b e P hP hel her hen K hz w hw
    x (py j) D.normX (D.normPY _) a c (D.cutX _ _ ha) (D.cutPY _ _ _ hc)
  have he (k : γ) : x k*φ a*w.eval φ b*φ c*b j*y k =
      (x k*φ a*w.eval φ b*φ c*py j k)*b j := by
    rw [D.matchedY (!j) hj k]
    simp only [mul_assoc,D.transferY]
  simpa only [he,zero_mul] using ht.mul tendsto_const_nhds

theorem bridge_left_term (w : BridgeCore F) (hw : w.Centered K)
    (hi : tx = some w.left) (c : F)
    (hc : ty ≠ some w.right ∨ f w.right c = 0) :
    Tendsto (fun k => x k*w.eval φ b*φ c*y k) l (𝓝 0) := by
  cases w with
  | single i =>
    have ht := D.crossX i c hi (D.exclude i hi)
    have he (k : γ) : x k*b i*φ c*y k = b i*(px (!i) k*φ c*y k) := by
      rw [D.matchedX i hi k,D.transferX]
      simp only [mul_assoc]
    simpa only [BridgeCore.eval,he,mul_zero] using
      (tendsto_const_nhds (x := b i)).mul ht
  | double i a j =>
    simpa only [BridgeCore.eval,mul_assoc] using
      bridge_left_transfer φ b e P hP hel her hen K hz D i hi (.single j) trivial a c hw hc
  | flank i a w d j =>
    have ht := bridge_left_transfer φ b e P hP hel her hen K hz D i hi
      (w.snoc d j) (w.centered_snoc K d j hw.2.2 hw.2.1) a c hw.1
      (by rw [BridgeCore.right_snoc]; exact hc)
    simpa only [BridgeCore.eval_snoc,BridgeCore.eval,mul_assoc] using ht

theorem bridge_right_term (w : BridgeCore F) (hw : w.Centered K)
    (hj : ty = some w.right) (a : F)
    (ha : tx ≠ some w.left ∨ f w.left a = 0) :
    Tendsto (fun k => x k*φ a*w.eval φ b*y k) l (𝓝 0) := by
  cases w with
  | single i =>
    have hne : tx ≠ some i := fun hi => D.exclude i hi hj
    have ht := D.crossY i a hj hne
    have he (k : γ) : x k*φ a*b i*y k = (x k*φ a*py i k)*b i := by
      rw [D.matchedY (!i) hj k]
      simp only [mul_assoc,D.transferY]
    simpa only [BridgeCore.eval,he,zero_mul] using
      ht.mul (tendsto_const_nhds (x := b i))
  | double i c j =>
    simpa only [BridgeCore.eval,mul_assoc] using
      bridge_right_transfer φ b e P hP hel her hen K hz D j hj (.single i) trivial a c hw ha
  | flank i c w d j =>
    have ht := bridge_right_transfer φ b e P hP hel her hen K hz D j hj
      (w.cons i c) (w.centered_cons K i c hw.1 hw.2.1) a d hw.2.2
      (by rw [BridgeCore.left_cons]; exact ha)
    simpa only [BridgeCore.eval_cons,BridgeCore.eval,mul_assoc] using ht

theorem bridge_both_term (w : BridgeCore F) (hw : w.Centered K)
    (hi : tx = some w.left) (hj : ty = some w.right) :
    Tendsto (fun k => x k*w.eval φ b*y k) l (𝓝 0) := by
  cases w with
  | single i => exact (D.exclude i hi hj).elim
  | double i a j =>
    have hne : (!j) ≠ (!i) := by
      intro h
      exact D.exclude i hi (hj.trans (congrArg some h))
    have heq : j = !i := by cases i <;> cases j <;> simp_all
    have ht := D.rectangle (!i) a hw
    have he (k : γ) : x k*(b i*φ a*b j)*y k =
        b i*(px (!i) k*φ a*py (!i) k)*b j := by
      rw [D.matchedX i hi k,D.matchedY (!j) hj k]
      calc
        _ = (px i k*b i)*φ a*(b j*py (!j) k) := by simp only [mul_assoc]
        _ = _ := by rw [D.transferX,D.transferY,heq]; simp only [mul_assoc]
    simpa only [BridgeCore.eval,he,mul_zero,zero_mul] using
      ((tendsto_const_nhds (x := b i)).mul ht).mul (tendsto_const_nhds (x := b j))
  | flank i a w c j =>
    have ht := supported_core_decay φ b e P hP hel her hen K hz w hw.2.1
      (px (!i)) (py j) (D.normPX _) (D.normPY _) a c
      (D.cutPX _ _ _ hw.1) (D.cutPY _ _ _ hw.2.2)
    have he (k : γ) : x k*(b i*φ a*w.eval φ b*φ c*b j)*y k =
        b i*(px (!i) k*φ a*w.eval φ b*φ c*py j k)*b j := by
      rw [D.matchedX i hi k,D.matchedY (!j) hj k]
      calc
        _ = (px i k*b i)*φ a*w.eval φ b*φ c*(b j*py (!j) k) := by simp only [mul_assoc]
        _ = _ := by rw [D.transferX,D.transferY]; simp only [mul_assoc]
    simpa only [BridgeCore.eval,he,mul_zero,zero_mul] using
      ((tendsto_const_nhds (x := b i)).mul ht).mul (tendsto_const_nhds (x := b j))

theorem bridge_word_decay (w : BridgeCore F) (hw : w.Centered K) (a c : F) :
    Tendsto (fun k => x k*φ a*w.eval φ b*φ c*y k) l (𝓝 0) := by
  let a' := bridgeZeroPart f tx w.left a
  let c' := bridgeZeroPart f ty w.right c
  let α := bridgeScalarPart f tx w.left a
  let β := bridgeScalarPart f ty w.right c
  have ha : tx ≠ some w.left ∨ f w.left a' = 0 := bridgeZeroPart_good f D.normState tx w.left a
  have hc : ty ≠ some w.right ∨ f w.right c' = 0 := bridgeZeroPart_good f D.normState ty w.right c
  have h00 := supported_core_decay φ b e P hP hel her hen K hz w hw
    x y D.normX D.normY a' c' (D.cutX _ _ ha) (D.cutY _ _ hc)
  have h10 : Tendsto (fun k => α • (x k*w.eval φ b*φ c'*y k)) l (𝓝 0) := by
    by_cases hi : tx = some w.left
    · simpa only [smul_zero] using
        (bridge_left_term φ b e P hP hel her hen K hz D w hw hi c' hc).const_smul α
    · simp only [α,bridgeScalarPart,ite_eq_right hi,zero_smul]
      exact tendsto_const_nhds
  have h01 : Tendsto (fun k => β • (x k*φ a'*w.eval φ b*y k)) l (𝓝 0) := by
    by_cases hj : ty = some w.right
    · simpa only [smul_zero] using
        (bridge_right_term φ b e P hP hel her hen K hz D w hw hj a' ha).const_smul β
    · simp only [β,bridgeScalarPart,ite_eq_right hj,zero_smul]
      exact tendsto_const_nhds
  have h11 : Tendsto (fun k => (α*β) • (x k*w.eval φ b*y k)) l (𝓝 0) := by
    by_cases hi : tx = some w.left
    · by_cases hj : ty = some w.right
      · simpa only [smul_zero] using
          (bridge_both_term φ b e P hP hel her hen K hz D w hw hi hj).const_smul (α*β)
      · simp only [β,bridgeScalarPart,ite_eq_right hj,mul_zero,zero_smul]
        exact tendsto_const_nhds
    · simp only [α,bridgeScalarPart,ite_eq_right hi,zero_mul,zero_smul]
      exact tendsto_const_nhds
  have ht := (h00.add h10).add (h01.add h11)
  have he (k : γ) := bridge_four_terms φ a c a' c' α β
    (bridge_split f tx w.left a) (bridge_split f ty w.right c) (x k) (y k) (w.eval φ b)
  simpa only [← he,add_zero] using ht

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev matrixState (i : Bool) := NaimarkZFC.matrixState (B.state i) i
abbrev matrixPeaks (i : Bool) : Peaks (B.matrixPeak i) (B.matrixState i) :=
  (B.peaks i).matrix (B.peak_zero i) i
abbrev matrixPure (i : Bool) : IsPureState (B.matrixState i) := (B.matrixPeaks i).isPureState
abbrev matrixTrace := matrixTraceState (n := Bool) (positiveCLM B.trace)
  (positiveCLM_isState B.trace B.normalized)

structure Endpoint (ι : Type*) [Preorder ι] where
  state : CStarMatrix Bool Bool A →L[ℂ] ℂ
  pure : IsPureState state
  net : ι → CStarMatrix Bool Bool A
  positive : ∀ k, 0 ≤ net k
  contractive : ∀ k, ‖net k‖ ≤ 1
  antitone : Antitone net
  excision : ∀ a, Tendsto (fun k => net k*(a-state a • 1)*net k) atTop (𝓝 0)
  trace_null : Tendsto (fun k => B.matrixTrace (net k)) atTop (𝓝 0)
  peakIndex : ι → ℕ
  peak_tendsto : Tendsto peakIndex atTop atTop
  tag : Option Bool
  matchedState : ∀ i, tag = some i → state = B.matrixState i
  matchedNet : ∀ i, tag = some i → ∀ k, net k = B.matrixPeak i (peakIndex k)
  unmatched : ∀ i, tag ≠ some i →
    ¬ UnitarilyEquivalent (pureGNS state pure) (pureGNS (B.matrixState i) (B.matrixPure i))

variable {B} {ι : Type*} [Preorder ι] (X : B.Endpoint ι)

theorem Endpoint.cut (i : Bool) (a : CStarMatrix Bool Bool A)
    (ha : X.tag ≠ some i ∨ B.matrixState i a = 0) :
    Tendsto (fun k => B.base (X.net k)*B.base a*B.support i*B.start) atTop (𝓝 0) := by
  have hcase : ¬ UnitarilyEquivalent (pureGNS X.state X.pure)
      (pureGNS (B.matrixState i) (B.matrixPure i)) ∨
      X.state = B.matrixState i ∧ B.matrixState i a = 0 := by
    by_cases h : X.tag = some i
    · exact Or.inr ⟨X.matchedState i h, ha.resolve_left (not_not.mpr h)⟩
    · exact Or.inl (X.unmatched i h)
  have ht := matrix_excision_square_endpoint B.peaks B.peak_zero (positiveCLM B.trace)
    (positiveCLM_isState B.trace B.normalized) B.atom_positive B.tracial i
    X.state X.pure X.net X.positive X.contractive X.antitone X.trace_null X.excision a hcase
  have he : Tendsto (fun k => B.expectation
      (star (X.net k*a*matrixSingle i i (1:A))*(X.net k*a*matrixSingle i i (1:A)))) atTop (𝓝 0) := by
    simpa only [B.expectation_eq] using ht
  have hb := atomicLeft_endpoint_tendsto B.atoms B.amalgam (by decide : false ≠ true)
    (fun k => X.net k*a*matrixSingle i i (1:A)) he
  simpa only [map_mul, support, bridgeSupport, base, start] using hb

theorem Endpoint.cut_right (i : Bool) (a : CStarMatrix Bool Bool A)
    (ha : X.tag ≠ some i ∨ B.matrixState i a = 0) :
    Tendsto (fun k => B.start*(B.support i*B.base a*B.base (X.net k))) atTop (𝓝 0) := by
  let : ContinuousStar B.Operators := ⟨ContinuousLinearMap.adjoint.continuous⟩
  have ha' : X.tag ≠ some i ∨ B.matrixState i (star a) = 0 := by
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (by rw [state_map_star _ (B.matrixPure i).1,ha,star_zero])
  have ht := (X.cut i (star a) ha').star
  have he (k : ι) : star (B.base (X.net k)*B.base (star a)*B.support i*B.start) =
      B.start*(B.support i*B.base a*B.base (X.net k)) := by
    rw [star_mul,star_mul,star_mul,(fockStartProjection_isProjection _ _).isSelfAdjoint.star_eq]
    rw [show star (B.support i) = B.support i from
      (IsStarProjection.map (matrixSingle_projection i (1:A) (by
        constructor <;> simp [IsIdempotentElem,IsSelfAdjoint])) B.base).isSelfAdjoint.star_eq]
    rw [← map_star,star_star,← map_star,(IsSelfAdjoint.of_nonneg (X.positive k)).star_eq]
    simp only [mul_assoc]
  rw [show star (0 : B.Operators) = 0 from map_zero ContinuousLinearMap.adjoint] at ht
  simpa only [he] using ht

def Separated : Prop := ∀ i j : Bool, i ≠ j →
  ¬ UnitarilyEquivalent (pureGNS (B.matrixState i) (B.matrixPure i))
    (pureGNS (B.matrixState j) (B.matrixPure j))

variable (B) in
theorem matrixPeak_trace_null (i : Bool) :
    Tendsto (fun n => B.matrixTrace (B.matrixPeak i n)) atTop (𝓝 0) := by
  have he (n : ℕ) : B.trace (B.peak i n) = ((B.trace (B.peak i n)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (B.trace.map_nonneg ((B.peaks i).1 n).nonneg).2.symm
  have ht : Tendsto (fun n => B.trace (B.peak i n)) atTop (𝓝 0) := by
    have ht := (Complex.continuous_ofReal.tendsto 0).comp (B.trace_null i)
    exact ht.congr' (Eventually.of_forall (fun n => (he n).symm))
  simpa only [matrixTrace,matrixPeak,matrixTraceState_single,positiveCLM_apply,smul_zero] using
    ht.const_smul (Fintype.card Bool : ℝ)⁻¹

variable (B) in

def peakEndpoint (hs : B.Separated) (i : Bool) : B.Endpoint ℕ where
  state := B.matrixState i
  pure := B.matrixPure i
  net := B.matrixPeak i
  positive n := ((B.matrixPeaks i).1 n).nonneg
  contractive n := ((B.matrixPeaks i).1 n).norm_le _
  antitone := (B.matrixPeaks i).2.1
  excision a := tendsto_zero_iff_norm_tendsto_zero.mpr ((B.matrixPeaks i).excision a)
  trace_null := B.matrixPeak_trace_null i
  peakIndex := id
  peak_tendsto := tendsto_id
  tag := some i
  matchedState j hj := by cases Option.some.inj hj; rfl
  matchedNet j hj := by cases Option.some.inj hj; intro; rfl
  unmatched j hj := hs i j (fun h => hj (congrArg some h))

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder
private theorem top_fst {ι κ : Type*} [Preorder ι] [Preorder κ] :
    Tendsto (Prod.fst : ι × κ → ι) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_fst

private theorem top_snd {ι κ : Type*} [Preorder ι] [Preorder κ] :
    Tendsto (Prod.snd : ι × κ → κ) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_snd

private theorem top_pair {ι κ μ : Type*} [Preorder ι] [Preorder κ]
    {l : Filter μ} {f : μ → ι} {g : μ → κ}
    (hf : Tendsto f l atTop) (hg : Tendsto g l atTop) :
    Tendsto (fun k => (f k,g k)) l atTop := by
  rw [← prod_atTop_atTop_eq]
  exact hf.prodMk hg

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem centered_state_zero (a : CStarMatrix Bool Bool A) (ha : B.expectation a = 0)
    (i : Bool) : B.matrixState i a = 0 := by
  exact matrix_centered_state_zero B.peaks (positiveCLM B.trace)
    (positiveCLM_isState B.trace B.normalized) B.atom_positive a
    (by simpa only [B.expectation_eq] using ha) i

variable {B} {ι κ : Type*} [Preorder ι] [Preorder κ]
  [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]
  (X : B.Endpoint ι) (Y : B.Endpoint κ)

theorem Endpoint.wordData (hs : B.Separated)
    (hex : ∀ i, X.tag = some i → Y.tag ≠ some (!i)) :
    BridgeDecayData B.base B.letter B.support B.start (fun a => B.expectation a = 0)
      (l := atTop) B.matrixState (fun k : ι × κ => B.base (X.net k.1))
      (fun k : ι × κ => B.base (Y.net k.2))
      (fun i k => B.base (B.matrixPeak i (X.peakIndex k.1)))
      (fun i k => B.base (B.matrixPeak i (Y.peakIndex k.2))) X.tag Y.tag where
  normX k := (NonUnitalStarAlgHom.norm_apply_le B.base _).trans (X.contractive _)
  normY k := (NonUnitalStarAlgHom.norm_apply_le B.base _).trans (Y.contractive _)
  normPX i k := (NonUnitalStarAlgHom.norm_apply_le B.base _).trans (((B.matrixPeaks i).1 _).norm_le _)
  normPY i k := (NonUnitalStarAlgHom.norm_apply_le B.base _).trans (((B.matrixPeaks i).1 _).norm_le _)
  normState i := ((isState_iff _).mp (B.matrixPure i).1).1
  matchedX i hi k := congrArg B.base (X.matchedNet i hi k.1)
  matchedY i hi k := congrArg B.base (Y.matchedNet i hi k.2)
  transferX i k := B.peak_transfer i (X.peakIndex k.1)
  transferY i k := (B.peak_transfer i (Y.peakIndex k.2)).symm
  exclude := hex
  cutX i a ha := (X.cut i a ha).comp top_fst
  cutY i a ha := (Y.cut_right i a ha).comp top_snd
  cutPX j i a ha := ((B.peakEndpoint hs j).cut i a (Or.inr (B.centered_state_zero a ha i))).comp
    (X.peak_tendsto.comp top_fst)
  cutPY j i a ha := ((B.peakEndpoint hs j).cut_right i a (Or.inr (B.centered_state_zero a ha i))).comp
    (Y.peak_tendsto.comp top_snd)
  crossX i a _ hj := by
    let hp := B.peakEndpoint hs (!i)
    have ht := state_cross_excision hp.state Y.state hp.pure Y.pure hp.net Y.net
      hp.positive hp.contractive Y.positive Y.contractive Y.antitone hp.excision Y.excision
      (fun h => Y.unmatched (!i) hj h.symm) a
    have hc : Tendsto (fun k : ι × κ => (X.peakIndex k.1,k.2)) atTop atTop :=
      top_pair (X.peak_tendsto.comp top_fst) top_snd
    have ho := ((map_continuous B.base).tendsto 0).comp (ht.comp hc)
    simpa only [Function.comp_def,hp,peakEndpoint,map_zero,map_mul] using ho
  crossY i a _ hi := by
    let hp := B.peakEndpoint hs i
    have ht := state_cross_excision X.state hp.state X.pure hp.pure X.net hp.net
      X.positive X.contractive hp.positive hp.contractive hp.antitone X.excision hp.excision
      (X.unmatched i hi) a
    have hc : Tendsto (fun k : ι × κ => (k.1,Y.peakIndex k.2)) atTop atTop :=
      top_pair top_fst (Y.peak_tendsto.comp top_snd)
    have ho := ((map_continuous B.base).tendsto 0).comp (ht.comp hc)
    simpa only [Function.comp_def,hp,peakEndpoint,map_zero,map_mul] using ho
  rectangle i a ha := by
    have ht := (B.matrixPeaks i).rectangular_excision a (B.centered_state_zero a ha i)
    have hc : Tendsto (fun k : ι × κ => (X.peakIndex k.1,Y.peakIndex k.2)) atTop atTop :=
      top_pair (X.peak_tendsto.comp top_fst)
        (Y.peak_tendsto.comp top_snd)
    have ho := ((map_continuous B.base).tendsto 0).comp (ht.comp hc)
    simpa only [Function.comp_def,map_zero,map_mul] using ho

theorem Endpoint.word_decay (hs : B.Separated)
    (hex : ∀ i, X.tag = some i → Y.tag ≠ some (!i))
    (w : BridgeCore (CStarMatrix Bool Bool A))
    (hw : w.Centered (fun a => B.expectation a = 0)) (a c : CStarMatrix Bool Bool A) :
    Tendsto (fun k : ι × κ => B.base (X.net k.1)*B.base a*w.eval B.base B.letter*
      B.base c*B.base (Y.net k.2)) atTop (𝓝 0) := by
  exact bridge_word_decay B.base B.letter B.support B.start
    (fockStartProjection_isProjection _ _) (bridgeLetter_support_left B.base B.aux B.diagonal B.diagonal_agree)
    (bridgeLetter_support_right B.base B.aux B.diagonal B.diagonal_agree) (bridgeSupport_norm B.base)
    (fun a => B.expectation a = 0) B.core_zero (X.wordData Y hs hex) w hw a c

end PeakingPairData

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule
section
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem representation_fix_of_coefficient_one
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖ = 1)
    (x : A) (hx : ‖x‖ ≤ 1) (hcoef : ⟪ξ, π x ξ⟫_ℂ = 1) : π x ξ = ξ := by
  have hbound : ‖π x ξ‖ ≤ 1 := by
    calc
      ‖π x ξ‖ ≤ ‖π x‖*‖ξ‖ := (π x).le_opNorm ξ
      _ ≤ ‖x‖*‖ξ‖ := mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le π x)
        (norm_nonneg ξ)
      _ ≤ 1 := by simpa only [hξ,mul_one] using hx
  have hd := norm_sub_sq (𝕜 := ℂ) ξ (π x ξ)
  rw [hξ,hcoef] at hd
  have hz : ‖ξ-π x ξ‖ = 0 := by
    simp only [RCLike.re_to_complex,Complex.one_re,one_pow] at hd
    nlinarith [norm_nonneg (ξ-π x ξ),norm_nonneg (π x ξ)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem representation_coefficient_compression
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) (x y a : A)
    (hx : IsSelfAdjoint x) (hfix : π x ξ = ξ) (hyfix : π y η = η) :
    ⟪ξ, π (x*a*y) η⟫_ℂ = ⟪ξ, π a η⟫_ℂ := by
  rw [map_mul,map_mul,mul_apply_eq_comp,mul_apply_eq_comp,hyfix,
    ← ContinuousLinearMap.adjoint_inner_left]
  have hs : (π x).adjoint = π x := by
    change star (π x) = π x
    rw [← map_star,hx.star_eq]
  rw [hs,hfix]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

omit [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] in

theorem state_two_compression (g : A →L[ℂ] ℂ) (hg : IsState g)
    (x y a : A) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hself : IsSelfAdjoint x)
    (hgx : g x = 1) (hgy : g y = 1) : g (x*a*y) = g a := by
  let f := positiveOfSquares g hg.2
  have hfx : f.gnsNonUnitalStarAlgHom x (gnsVector f) = gnsVector f :=
    gns_fix_of_value_one f ((isState_iff g).mp hg).1 x hx hgx
  have hfy : f.gnsNonUnitalStarAlgHom y (gnsVector f) = gnsVector f :=
    gns_fix_of_value_one f ((isState_iff g).mp hg).1 y hy hgy
  have he := representation_coefficient_compression f.gnsNonUnitalStarAlgHom
    (gnsVector f) (gnsVector f) x y a hself hfx hfy
  change ⟪gnsVector f, f.gnsStarAlgHom (x*a*y) (gnsVector f)⟫_ℂ =
    ⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ at he
  rw [gnsVector_coefficient,gnsVector_coefficient] at he
  exact he

omit [PartialOrder A] [StarOrderedRing A] in

theorem unique_extension_of_dense_word_decay {ι : Type*} {l : Filter ι} [l.NeBot]
    (φ : A →⋆ₐ[ℂ] B) (h : A →L[ℂ] ℂ) (W : Set B)
    (hdense : Dense (Submodule.span ℂ (Set.range φ ∪ W) : Set B))
    (x : ι → A) (hx : ∀ i, ‖x i‖ ≤ 1) (hself : ∀ i, IsSelfAdjoint (x i))
    (hxval : ∀ i, h (x i) = 1)
    (hdecay : ∀ w ∈ W, Tendsto (fun i => φ (x i)*w*φ (x i)) l (𝓝 0))
    (g₁ g₂ : B →L[ℂ] ℂ) (hg₁ : IsState g₁) (hg₂ : IsState g₂)
    (hres₁ : restrictState φ g₁ = h) (hres₂ : restrictState φ g₂ = h) : g₁ = g₂ := by
  have hzero (g : B →L[ℂ] ℂ) (hg : IsState g) (hres : restrictState φ g = h)
      (w : B) (hw : w ∈ W) : g w = 0 := by
    have hc (i : ι) : g (φ (x i)*w*φ (x i)) = g w :=
      state_compression g hg (φ (x i))
        ((NonUnitalStarAlgHom.norm_apply_le φ _).trans (hx i))
        ((hself i).map φ) (by
          change restrictState φ g (x i) = 1
          rw [hres,hxval]) w
    have ht := g.continuous.tendsto 0 |>.comp (hdecay w hw)
    have ht' : Tendsto (fun _ : ι => g w) l (𝓝 (0 : ℂ)) := by
      simpa only [Function.comp_def,hc,map_zero] using ht
    exact tendsto_nhds_unique tendsto_const_nhds ht'
  apply ContinuousLinearMap.ext_on hdense
  intro b hb
  rcases hb with ⟨a,rfl⟩ | hw
  · change restrictState φ g₁ a = restrictState φ g₂ a
    rw [hres₁,hres₂]
  · rw [hzero g₁ hg₁ hres₁ b hw,hzero g₂ hg₂ hres₂ b hw]

omit [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] in

theorem no_common_irrep_of_dense_decay {ι : Type*} {l : Filter ι} [l.NeBot]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (hξ : ξ ≠ 0) (hη : η ≠ 0) (S : Set A)
    (hdense : Dense (Submodule.span ℂ S : Set A)) (x y : ι → A)
    (hself : ∀ i, IsSelfAdjoint (x i))
    (hfix : ∀ i, π (x i) ξ = ξ) (hyfix : ∀ i, π (y i) η = η)
    (hdecay : ∀ a ∈ S, Tendsto (fun i => x i*a*y i) l (𝓝 0)) : False := by
  let F : A →L[ℂ] ℂ := (innerSL ℂ ξ).comp (orbitCLM π η)
  have hF : F = 0 := by
    apply ContinuousLinearMap.ext_on hdense
    intro a ha
    have he (i : ι) : F (x i*a*y i) = F a :=
      representation_coefficient_compression π ξ η _ _ _ (hself i) (hfix i) (hyfix i)
    have ht : Tendsto (fun _ : ι => F a) l (𝓝 (0 : ℂ)) := by
      simpa only [Function.comp_def,he,map_zero] using (F.continuous.tendsto 0).comp (hdecay a ha)
    exact tendsto_nhds_unique tendsto_const_nhds ht
  have hc (a : A) : ⟪ξ, π a η⟫_ℂ = 0 := congrArg (fun f : A →L[ℂ] ℂ => f a) hF
  have hz : ⟪ξ,ξ⟫_ℂ = 0 := (irreducible_vector_cyclic π hπ η hη).induction_on (p := fun v => ⟪ξ,v⟫_ℂ = 0) ξ
    (isClosed_eq (innerSL ℂ ξ).continuous continuous_const) hc
  exact hξ (inner_self_eq_zero.mp hz)

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : PeakingPairData A} {ι κ : Type*} [Preorder ι] [Preorder κ]
  [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]
  (X : B.Endpoint ι) (Y : B.Endpoint κ)

theorem Endpoint.model_word_decay (hs : B.Separated)
    (hex : ∀ i, X.tag = some i → Y.tag ≠ some (!i))
    (w : BridgeCore (CStarMatrix Bool Bool A))
    (hw : w.Centered (fun a => B.expectation a = 0)) (a c : CStarMatrix Bool Bool A) :
    Tendsto (fun k : ι × κ => B.embedBase (X.net k.1)*B.embedBase a*
      w.eval B.embedBase B.modelLetter*B.embedBase c*B.embedBase (Y.net k.2)) atTop (𝓝 0) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun k : ι × κ => B.base (X.net k.1)*B.base a*
    (↑(w.eval B.embedBase B.modelLetter : B.Model) : B.Operators)*B.base c*B.base (Y.net k.2))
    atTop (𝓝 0)
  simpa only [B.coe_core] using X.word_decay Y hs hex w hw a c

theorem Endpoint.unique_matrix_extension (hs : B.Separated)
    (hval : ∀ k, X.state (X.net k) = 1)
    (g₁ g₂ : B.Model →L[ℂ] ℂ) (hg₁ : IsState g₁) (hg₂ : IsState g₂)
    (hr₁ : restrictState B.embedBase g₁ = X.state)
    (hr₂ : restrictState B.embedBase g₂ = X.state) : g₁ = g₂ := by
  let W : Set B.Model := {z | ∃ (w : BridgeCore (CStarMatrix Bool Bool A))
    (a c : CStarMatrix Bool Bool A), w.Centered (fun d => B.expectation d = 0) ∧
      z = B.embedBase a*w.eval B.embedBase B.modelLetter*B.embedBase c}
  apply unique_extension_of_dense_word_decay (l := atTop) B.embedBase X.state W B.model_words_dense
    X.net X.contractive (fun k => IsSelfAdjoint.of_nonneg (X.positive k)) hval ?_
    g₁ g₂ hg₁ hg₂ hr₁ hr₂
  rintro z ⟨w,a,c,hw,rfl⟩
  have hex : ∀ i, X.tag = some i → X.tag ≠ some (!i) := by
    intro i hi
    rw [hi]
    cases i <;> simp
  have ht := (X.model_word_decay X hs hex w hw a c).comp tendsto_atTop_diagonal
  simpa only [Function.comp_def,mul_assoc] using ht

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
section

variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

theorem simple_nonzeroStarHom_injective (hA : IsSimpleCStar A)
    (φ : A →⋆ₙₐ[ℂ] C) (hne : φ ≠ 0) : Function.Injective φ := by
  have hc : IsClosed (TwoSidedIdeal.ker φ : Set A) := by
    have he : (TwoSidedIdeal.ker φ : Set A) = {a : A | φ a = 0} := by
      ext a; exact TwoSidedIdeal.mem_ker φ
    rw [he]
    exact isClosed_eq (map_continuous φ) continuous_const
  rcases hA.2 (TwoSidedIdeal.ker φ) hc with hb | ht
  · exact (TwoSidedIdeal.ker_eq_bot φ).mp hb
  · exfalso
    apply hne
    ext a
    apply (TwoSidedIdeal.mem_ker φ).mp
    rw [ht]
    exact TwoSidedIdeal.mem_top _

variable [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in

theorem simple_matrix_corner_injective (hA : IsSimpleCStar A)
    (π : CStarMatrix Bool Bool A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (i : Bool)
    (hne : π (matrixSingle i i (1 : A)) ≠ 0) :
    Function.Injective (π.comp (matrixSingleHom i)) := by
  apply simple_nonzeroStarHom_injective hA
  intro he
  apply hne
  exact congrArg (fun φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H) => φ 1) he

theorem matrix_pure_corner_ne_zero (f : A →L[ℂ] ℂ) (hf : IsPureState f) (i : Bool) :
    pureGNS (matrixState f i) (matrixState_isPureState f hf i)
      (matrixSingle i i (1 : A)) ≠ 0 := by
  let F := positiveOfSquares (matrixState f i) (matrixState_isState f hf.1 i).2
  intro hz
  have hc := gnsVector_coefficient F (matrixSingle i i (1:A))
  change ⟪gnsVector F,
    pureGNS (matrixState f i) (matrixState_isPureState f hf i)
      (matrixSingle i i (1:A)) (gnsVector F)⟫_ℂ = matrixState f i (matrixSingle i i 1) at hc
  rw [hz,zero_apply,inner_zero_right] at hc
  simp only [matrixState_apply,matrixSingle_apply,ite_true,true_and] at hc
  exact zero_ne_one (hc.trans ((isState_iff f).mp hf.1).1)

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev pureIndex (_B : PeakingPairData A) (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f) :=
  ExcisionIndex (vectorNullAlgebra (pureGNS f hf)
    (gnsVector (positiveOfSquares f hf.1.2))) × ℕ

instance pureIndexDirected (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f) :
    IsDirectedOrder (B.pureIndex f hf) := ⟨by
  intro x y
  obtain ⟨z,hxz,hyz⟩ := exists_ge_ge x.1 y.1
  exact ⟨(z,max x.2 y.2),⟨hxz,le_max_left _ _⟩,⟨hyz,le_max_right _ _⟩⟩⟩

def otherEndpoint (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS f hf p ≠ 0 ∧ (B.matrixTrace p).re < ε)
    (hne : ∀ i, ¬ UnitarilyEquivalent (pureGNS f hf)
      (pureGNS (B.matrixState i) (B.matrixPure i))) : B.Endpoint (B.pureIndex f hf) :=
  let π := pureGNS f hf
  let ξ := gnsVector (positiveOfSquares f hf.1.2)
  have hπ := pure_gns_irreducible f hf.1 hf
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one _ ((isState_iff f).mp hf.1).1
  have ht : Tendsto (fun k : B.pureIndex f hf => k.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]; exact tendsto_fst
  { state := f
    pure := hf
    net := fun k => pureExcisionNet π ξ k.1
    positive k := pureExcisionNet_nonneg π ξ k.1
    contractive k := pureExcisionNet_norm π ξ k.1
    antitone := fun _ _ h => (pureExcisionNet_antitone π ξ) h.1
    excision a := by
      have he := (pureExcisionNet_excision π hπ ξ hξ a).comp ht
      have hc (a) : ⟪ξ, π a ξ⟫_ℂ = f a := gnsVector_coefficient _ a
      simpa only [Function.comp_def,hc] using he
    trace_null := by
      apply (pureExcisionNet_trace_null π hπ ξ hξ B.matrixTrace
        (matrixTraceState_isState (positiveCLM B.trace)
          (positiveCLM_isState B.trace B.normalized)) ?_ hsmall).comp ht
      intro M N
      exact matrixTraceState_tracial (positiveCLM B.trace)
        (positiveCLM_isState B.trace B.normalized) B.tracial M N
    peakIndex := Prod.snd
    peak_tendsto := by rw [← prod_atTop_atTop_eq]; exact tendsto_snd
    tag := none
    matchedState i hi := by cases hi
    matchedNet i hi := by cases hi
    unmatched i _ := hne i }

theorem otherEndpoint_value_one (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS f hf p ≠ 0 ∧ (B.matrixTrace p).re < ε)
    (hne : ∀ i, ¬ UnitarilyEquivalent (pureGNS f hf)
      (pureGNS (B.matrixState i) (B.matrixPure i))) (k : B.pureIndex f hf) :
    (B.otherEndpoint f hf hsmall hne).state ((B.otherEndpoint f hf hsmall hne).net k) = 1 := by
  let F := positiveOfSquares f hf.1.2
  have hh := pureExcisionNet_fixes (pureGNS f hf) (map_one F.gnsStarAlgHom) (gnsVector F) k.1
  change f (pureExcisionNet (pureGNS f hf) (gnsVector F) k.1) = 1
  change F (pureExcisionNet (pureGNS f hf) (gnsVector F) k.1) = 1
  rw [← gnsVector_coefficient F]
  change ⟪gnsVector F,pureGNS f hf (pureExcisionNet (pureGNS f hf) (gnsVector F) k.1)
    (gnsVector F)⟫_ℂ = 1
  rw [hh,inner_self_eq_norm_sq_to_K,gnsVector_norm_eq_one F ((isState_iff f).mp hf.1).1]
  norm_num

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
theorem matrixSingle_representation_ne_zero
    {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]
    (π : CStarMatrix Bool Bool A →⋆ₙₐ[ℂ] C) (i : Bool)
    (hinj : Function.Injective (π.comp (matrixSingleHom i))) {a : A} (ha : a ≠ 0) :
    π (matrixSingle i i a) ≠ 0 := by
  intro hz
  apply ha
  apply hinj
  change π (matrixSingle i i a) = π (matrixSingle i i (0:A))
  rw [hz,matrixSingle_zero,map_zero]

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem supported_small_projections (hA : IsSimpleCStar A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (i : Bool) :
    ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧
      pureGNS (NaimarkZFC.matrixState f i) (matrixState_isPureState f hf i) p ≠ 0 ∧
      (B.matrixTrace p).re < ε := by
  let π := pureGNS (NaimarkZFC.matrixState f i) (matrixState_isPureState f hf i)
  have hinj := simple_matrix_corner_injective hA π i (matrix_pure_corner_ne_zero f hf i)
  have he (n : ℕ) : (B.matrixTrace (matrixSingle i i (B.peak false n))).re =
      (Fintype.card Bool : ℝ)⁻¹ * (B.trace (B.peak false n)).re := by
    simp only [matrixTrace,matrixTraceState_single,positiveCLM_apply]
    exact Complex.smul_re _ _
  have ht : Tendsto (fun n => (B.matrixTrace (matrixSingle i i (B.peak false n))).re)
      atTop (𝓝 0) := by
    simpa only [he,mul_zero] using (B.trace_null false).const_mul (Fintype.card Bool : ℝ)⁻¹
  intro ε hε
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨matrixSingle i i (B.peak false n),
    matrixSingle_projection i _ ((B.peaks false).1 n), ?_, hn⟩
  apply matrixSingle_representation_ne_zero π i hinj
  intro hp
  have hv := (B.peaks false).2.2.2.1 n
  rw [hp,map_zero] at hv
  exact zero_ne_one hv

end PeakingPairData

open scoped CStarAlgebra ComplexOrder InnerProductSpace
section
universe u v
variable {A : Type u} {C : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

def StateExtensionUnique (φ : A →⋆ₐ[ℂ] C) (f : A →L[ℂ] ℂ) : Prop :=
  ∀ g₁ g₂ : C →L[ℂ] ℂ, IsState g₁ → IsState g₂ →
    restrictState φ g₁ = f → restrictState φ g₂ = f → g₁ = g₂

omit [PartialOrder A] [StarOrderedRing A] in

theorem StateExtensionUnique.transport {φ : A →⋆ₐ[ℂ] C} {f : A →L[ℂ] ℂ}
    (hu : StateExtensionUnique φ f) (α : A ≃⋆ₐ[ℂ] A) (β : C ≃⋆ₐ[ℂ] C)
    (hc : ∀ a, φ (α a) = β (φ a)) :
    StateExtensionUnique φ (restrictState α.toStarAlgHom f) := by
  have hs (a : A) : φ (α.symm a) = β.symm (φ a) := by
    apply β.injective
    change β (φ (α.symm a)) = β (β.symm (φ a))
    rw [β.apply_symm_apply,← hc,α.apply_symm_apply]
  intro g₁ g₂ hg₁ hg₂ hr₁ hr₂
  have hres (g : C →L[ℂ] ℂ) (hr : restrictState φ g = restrictState α.toStarAlgHom f) :
      restrictState φ (restrictState β.symm.toStarAlgHom g) = f := by
    ext a
    change g (β.symm (φ a)) = f a
    rw [← hs]
    change restrictState φ g (α.symm a) = f a
    rw [hr]
    change f (α (α.symm a)) = f a
    rw [α.apply_symm_apply]
  have he := hu _ _ (isState_restrict _ _ hg₁) (isState_restrict _ _ hg₂)
    (hres g₁ hr₁) (hres g₂ hr₂)
  ext c
  have hh := congrArg (fun g : C →L[ℂ] ℂ => g (β c)) he
  change g₁ (β.symm (β c)) = g₂ (β.symm (β c)) at hh
  simpa only [β.symm_apply_apply] using hh

theorem pureState_equivalent_conjugate (f h : A →L[ℂ] ℂ)
    (hf : IsPureState f) (hh : IsPureState h)
    (he : UnitarilyEquivalent (pureGNS f hf) (pureGNS h hh)) :
    ∃ u : unitary A, h = restrictState (Unitary.conjStarAlgAut ℂ A u).symm.toStarAlgHom f := by
  let F := positiveOfSquares f hf.1.2
  let G := positiveOfSquares h hh.1.2
  obtain ⟨u,hu⟩ := equivalent_vector_states_unitary (pureGNS f hf)
    (pure_gns_irreducible f hf.1 hf) (pureGNS h hh) he (gnsVector F) (gnsVector G)
    (gnsVector_norm_eq_one F ((isState_iff f).mp hf.1).1)
    (gnsVector_norm_eq_one G ((isState_iff h).mp hh.1).1)
  refine ⟨u, ?_⟩
  ext a
  have hF (a : A) : ⟪gnsVector F, pureGNS f hf a (gnsVector F)⟫_ℂ = f a :=
    gnsVector_coefficient F a
  have hG (a : A) : ⟪gnsVector G, pureGNS h hh a (gnsVector G)⟫_ℂ = h a :=
    gnsVector_coefficient G a
  change h a = f (star (u:A)*a*(u:A))
  simpa only [hF,hG] using hu a

theorem StateExtensionUnique.of_equivalent {φ : A →⋆ₐ[ℂ] C}
    {f h : A →L[ℂ] ℂ} (hu : StateExtensionUnique φ f)
    (hf : IsPureState f) (hh : IsPureState h)
    (he : UnitarilyEquivalent (pureGNS f hf) (pureGNS h hh)) :
    StateExtensionUnique φ h := by
  obtain ⟨u,rfl⟩ := pureState_equivalent_conjugate f h hf hh he
  let v : unitary C := ⟨φ (u : A), by
    constructor
    · rw [← map_star,← map_mul,u.property.1,map_one]
    · rw [← map_star,← map_mul,u.property.2,map_one]⟩
  apply hu.transport (Unitary.conjStarAlgAut ℂ A u).symm
    (Unitary.conjStarAlgAut ℂ C v).symm
  intro a
  change φ (star (u:A)*a*(u:A)) = star (φ (u:A))*φ a*φ (u:A)
  simp only [map_mul,map_star]

omit [PartialOrder A] [StarOrderedRing A] in

theorem pure_extensions_inequivalent_of_no_common
    (φ : A →⋆ₐ[ℂ] C) (f h : A →L[ℂ] ℂ)
    (hno : ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      ∀ (π : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)), IsIrreducible π →
      ∀ ξ η : H, ‖ξ‖ = 1 → ‖η‖ = 1 →
      (∀ a, ⟪ξ,π (φ a) ξ⟫_ℂ = f a) →
      (∀ a, ⟪η,π (φ a) η⟫_ℂ = h a) → False)
    (g₁ g₂ : C →L[ℂ] ℂ) (hg₁ : IsPureState g₁) (hg₂ : IsPureState g₂)
    (hr₁ : restrictState φ g₁ = f) (hr₂ : restrictState φ g₂ = h) :
    ¬ UnitarilyEquivalent (pureGNS g₁ hg₁) (pureGNS g₂ hg₂) := by
  rintro ⟨U,hU⟩
  let F := positiveOfSquares g₁ hg₁.1.2
  let G := positiveOfSquares g₂ hg₂.1.2
  have hF := gnsVector_norm_eq_one F ((isState_iff g₁).mp hg₁.1).1
  have hG := gnsVector_norm_eq_one G ((isState_iff g₂).mp hg₂.1).1
  apply hno G.GNS (pureGNS g₂ hg₂) (pure_gns_irreducible g₂ hg₂.1 hg₂)
    (U (gnsVector F)) (gnsVector G) (by rw [U.norm_map,hF]) hG
  · intro a
    rw [← hU (φ a) (gnsVector F),U.inner_map_map]
    change ⟪gnsVector F,F.gnsStarAlgHom (φ a) (gnsVector F)⟫_ℂ = f a
    rw [gnsVector_coefficient]
    exact congrArg (fun k : A →L[ℂ] ℂ => k a) hr₁
  · intro a
    change ⟪gnsVector G,G.gnsStarAlgHom (φ a) (gnsVector G)⟫_ℂ = h a
    rw [gnsVector_coefficient]
    exact congrArg (fun k : A →L[ℂ] ℂ => k a) hr₂

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem matrix_unique_of_small (hs : B.Separated)
    (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS f hf p ≠ 0 ∧ (B.matrixTrace p).re < ε) :
    StateExtensionUnique B.embedBase f := by
  classical
  by_cases he : ∃ i, UnitarilyEquivalent (pureGNS (B.matrixState i) (B.matrixPure i))
      (pureGNS f hf)
  · obtain ⟨i,hi⟩ := he
    have hu : StateExtensionUnique B.embedBase (B.matrixState i) :=
      (B.peakEndpoint hs i).unique_matrix_extension hs (fun n => (B.matrixPeaks i).2.2.2.1 n)
    exact hu.of_equivalent (B.matrixPure i) hf hi
  · have hne : ∀ i, ¬ UnitarilyEquivalent (pureGNS f hf)
        (pureGNS (B.matrixState i) (B.matrixPure i)) := by
      intro i hi
      exact he ⟨i, UnitarilyEquivalent.symm hi⟩
    exact (B.otherEndpoint f hf hsmall hne).unique_matrix_extension hs
      (B.otherEndpoint_value_one f hf hsmall hne)

theorem supported_matrix_unique (hs : B.Separated) (hA : IsSimpleCStar A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (i : Bool) :
    StateExtensionUnique B.embedBase (NaimarkZFC.matrixState f i) :=
  B.matrix_unique_of_small hs _ (matrixState_isPureState f hf i)
    (B.supported_small_projections hA f hf i)

end PeakingPairData

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]
  [PartialOrder A] [StarOrderedRing A]

theorem isState_of_unital_contractive_hermitian (f : A →L[ℂ] ℂ)
    (h1 : f 1 = 1) (hn : ∀ a, ‖f a‖ ≤ ‖a‖)
    (hstar : ∀ a, f (star a) = star (f a)) : IsState f := by
  let sa : selfAdjoint A →L[ℝ] A :=
    ((selfAdjoint.submodule ℝ A).subtype).mkContinuous 1 (fun a => by simp)
  let g : selfAdjoint A →L[ℝ] ℝ := Complex.reCLM.comp ((f.restrictScalars ℝ).comp sa)
  have hg : ‖g‖ ≤ 1 := by
    apply g.opNorm_le_bound zero_le_one
    intro a
    change ‖(f (a:A)).re‖ ≤ 1*‖a‖
    rw [one_mul,Real.norm_eq_abs]
    change |(f (a:A)).re| ≤ ‖(a:A)‖
    exact (Complex.abs_re_le_norm _).trans (hn a)
  apply (isState_iff f).mpr
  refine ⟨h1,fun a => ?_⟩
  have hsa : IsSelfAdjoint (star a*a) := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg a)
  have hi : (f (star a*a)).im = 0 := by
    have hh := hstar (star a*a)
    rw [hsa.star_eq] at hh
    exact Complex.conj_eq_iff_im.mp hh.symm
  refine ⟨hi,?_⟩
  exact selfAdjoint_nonneg_of_norm_one g hg (by change (f 1).re = 1; rw [h1]; rfl)
    ⟨star a*a,hsa⟩ (star_mul_self_nonneg a)

variable (e : A) (he : IsStarProjection e)

omit [PartialOrder A] [StarOrderedRing A] in

theorem cornerCompression_norm (a : A) : ‖cornerCompression e he a‖ ≤ ‖a‖ := by
  change ‖e*a*e‖ ≤ ‖a‖
  calc
    _ ≤ (‖e‖*‖a‖)*‖e‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖a‖)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (he.norm_le e) (norm_nonneg _)) (he.norm_le e)
      (norm_nonneg _) (by positivity)
    _ = ‖a‖ := by ring

def cornerLiftState (g : CStarCorner e he →L[ℂ] ℂ) : A →L[ℂ] ℂ :=
  g.comp (cornerCompression e he)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cornerLiftState_apply (g : CStarCorner e he →L[ℂ] ℂ) (a : A) :
    cornerLiftState e he g a = g (cornerCompression e he a) := rfl

theorem cornerLiftState_isState (g : CStarCorner e he →L[ℂ] ℂ) (hg : IsState g) :
    IsState (cornerLiftState e he g) := by
  apply isState_of_unital_contractive_hermitian
  · change g (cornerCompression e he (1:A)) = 1
    have h : cornerCompression e he (1:A) = 1 := by
      apply Subtype.ext
      change e*1*e=e
      rw [mul_one,he.isIdempotentElem.eq]
    rw [h,((isState_iff g).mp hg).1]
  · intro a
    exact (state_norm_apply_le g hg _).trans (cornerCompression_norm e he a)
  · intro a
    have h : cornerCompression e he (star a) = star (cornerCompression e he a) := by
      apply Subtype.ext
      change e*star a*e=star (e*a*e)
      simp only [star_mul,he.isSelfAdjoint.star_eq,mul_assoc]
    change g (cornerCompression e he (star a)) = star (g (cornerCompression e he a))
    rw [h,state_map_star g hg]

variable [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder C] [StarOrderedRing C] in

theorem matrixCorner_compression (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
    (M : CStarMatrix Bool Bool A) :
    cornerCompression (matrixCornerProjection φ) (matrixCornerProjection_isProjection φ) (φ M) =
      matrixCornerBase φ (M false false) := by
  apply Subtype.ext
  change φ (matrixSingle false false (1:A))*φ M*φ (matrixSingle false false (1:A)) =
    φ (matrixSingle false false (M false false))
  rw [← map_mul,← map_mul,matrixSingle_compress,one_mul,mul_one]

theorem corner_unique_of_matrix (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
    (f : A →L[ℂ] ℂ) (hu : StateExtensionUnique φ (matrixState f false)) :
    StateExtensionUnique (matrixCornerBase φ) f := by
  intro g₁ g₂ hg₁ hg₂ hr₁ hr₂
  let e := matrixCornerProjection φ
  let he := matrixCornerProjection_isProjection φ
  have hres (g : MatrixHNNCorner φ →L[ℂ] ℂ) (hr : restrictState (matrixCornerBase φ) g = f) :
      restrictState φ (cornerLiftState e he g) = matrixState f false := by
    ext M
    change g (cornerCompression e he (φ M)) = f (M false false)
    rw [matrixCorner_compression]
    exact congrArg (fun k : A →L[ℂ] ℂ => k (M false false)) hr
  have hh := hu _ _ (cornerLiftState_isState e he g₁ hg₁)
    (cornerLiftState_isState e he g₂ hg₂) (hres g₁ hr₁) (hres g₂ hr₂)
  ext a
  have ha := congrArg (fun k : C →L[ℂ] ℂ => k (a:C)) hh
  simpa only [cornerLiftState_apply,cornerCompression_corner] using ha

end

section
variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

theorem exists_state_extension_of_injective (φ : A →⋆ₐ[ℂ] C)
    (hφ : Function.Injective φ) (f : A →L[ℂ] ℂ) (hf : IsState f) :
    ∃ g : C →L[ℂ] ℂ, IsState g ∧ restrictState φ g = f := by
  let : IsClosed (φ.range : Set C) :=
    (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosed_range
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder φ.range := CStarAlgebra.spectralOrder φ.range
  let : StarOrderedRing φ.range := CStarAlgebra.spectralOrderedRing φ.range
  let e := StarAlgEquiv.ofInjective φ hφ
  let h := restrictState e.symm.toStarAlgHom f
  obtain ⟨g,hg,hres⟩ := exists_state_extension_subalgebra φ.range h
    (isState_restrict _ _ hf)
  refine ⟨g,hg,?_⟩
  ext a
  have hh := hres (e a)
  change g (φ a) = f a
  change g (φ a) = f (e.symm (e a)) at hh
  simpa only [e.symm_apply_apply] using hh

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder C] [StarOrderedRing C]

theorem StateExtensionUnique.exists_unique_pure {φ : A →⋆ₐ[ℂ] C}
    (hφ : Function.Injective φ) {f : A →L[ℂ] ℂ} (hf : IsPureState f)
    (hu : StateExtensionUnique φ f) :
    ∃ g : C →L[ℂ] ℂ, IsPureState g ∧ restrictState φ g = f ∧
      ∀ h : C →L[ℂ] ℂ, IsState h → restrictState φ h = f → h = g := by
  obtain ⟨g,hg,hr⟩ := exists_state_extension_of_injective φ hφ f hf.1
  have huniq : ∀ h : C →L[ℂ] ℂ, IsState h → restrictState φ h = f → h = g :=
    fun h hh hhr => hu h g hh hg hhr hr
  exact ⟨g,unique_lift_pure φ f hf g hg hr huniq,hr,huniq⟩

end

end NaimarkZFC

end

end OAI
