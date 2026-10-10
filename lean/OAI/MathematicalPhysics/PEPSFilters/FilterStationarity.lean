import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.Phases
import OAI.MathematicalPhysics.PEPSFilters.UnitaryVariation

namespace OAI

/-! Local stationarity, trace stripping and commutation of maximizing filters. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder

namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped Matrix.Norms.L2Operator MatrixOrder

lemma matrixOutput_add {L q m : ℕ} (T : Fin m → Operator L q) (v w : State L q) :
    matrixOutput T (v + w) = matrixOutput T v + matrixOutput T w := by
  induction m generalizing v w with
  | zero => rfl
  | succ m ih =>
    simp only [matrixOutput_succ, map_add]
    exact ih _ _ _

lemma matrixOutput_smul {L q m : ℕ} (T : Fin m → Operator L q) (c : ℂ) (v : State L q) :
    matrixOutput T (c • v) = c • matrixOutput T v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    simp only [matrixOutput_succ, map_smul]
    exact ih _ _

lemma matrixOutput_update_add {L q m : ℕ} (T : Fin m → Operator L q)
    (v : State L q) (j : Fin m) (A B : Operator L q) :
    matrixOutput (Function.update T j (A+B)) v =
      matrixOutput (Function.update T j A) v + matrixOutput (Function.update T j B) v := by
  classical
  induction m generalizing v with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [matrixOutput_succ, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _)]
      change matrixOutput (fun k : Fin m => T k.succ) (asMap (A+B) v) = _
      rw [show asMap (A+B) v = asMap A v + asMap B v from by
        change (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) (A+B)) v = _
        rw [map_add]; rfl, matrixOutput_add]
    · simp only [matrixOutput_succ, Function.update_of_ne (Fin.succ_ne_zero _).symm]
      have hupdate (C : Operator L q) :
          (fun s : Fin m => Function.update T k.succ C s.succ) =
            Function.update (fun s => T s.succ) k C := by
        funext s
        by_cases hs : s = k
        · subst s; simp
        · simp [Function.update_of_ne hs, Function.update_of_ne (fun h => hs (Fin.succ_inj.mp h))]
      simp only [hupdate]
      exact ih _ _ _

lemma matrixOutput_update_smul {L q m : ℕ} (T : Fin m → Operator L q)
    (v : State L q) (j : Fin m) (c : ℂ) (A : Operator L q) :
    matrixOutput (Function.update T j (c • A)) v =
      c • matrixOutput (Function.update T j A) v := by
  classical
  induction m generalizing v with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [matrixOutput_succ, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _)]
      change matrixOutput (fun k : Fin m => T k.succ) (asMap (c • A) v) = _
      rw [show asMap (c • A) v = c • asMap A v from by
        change (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) (c • A)) v = _
        rw [map_smul]; rfl, matrixOutput_smul]
    · simp only [matrixOutput_succ, Function.update_of_ne (Fin.succ_ne_zero _).symm]
      have hupdate (C : Operator L q) :
          (fun s : Fin m => Function.update T k.succ C s.succ) =
            Function.update (fun s => T s.succ) k C := by
        funext s
        by_cases hs : s = k
        · subst s; simp
        · simp [Function.update_of_ne hs, Function.update_of_ne (fun h => hs (Fin.succ_inj.mp h))]
      simp only [hupdate]
      exact ih _ _ _

def insertionMap {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (F : FilterFamily q m X) (v : State L q) (j : Fin m) :
    Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ →ₗ[ℂ] State L q :=
  let e : Operator L q →ₗ[ℂ] State L q := {
    toFun := fun A => matrixOutput (Function.update (fun k => liftLocal (X k) (F k).matrix) j A) v
    map_add' := matrixOutput_update_add _ v j
    map_smul' := fun c A => matrixOutput_update_smul _ v j c A }
  e.comp (liftLocalHom (q := q) (X j)).toLinearMap

lemma insertionMap_self {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (F : FilterFamily q m X) (v : State L q) (j : Fin m) :
    insertionMap F v j (F j).matrix = output F v := by
  change matrixOutput (Function.update (fun k => liftLocal (X k) (F k).matrix) j
    (liftLocal (X j) (F j).matrix)) v = output F v
  rw [Function.update_eq_self]
  rfl

lemma IsMaximizer.insertion_unitary_max {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    {a : Fin m → ℝ} {Ω : State L q} {F : FilterFamily q m X}
    (hF : IsMaximizer Ω a F) (j : Fin m)
    (U : unitary (Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ)) :
    ‖insertionMap F Ω j ((U : Matrix _ _ ℂ) * (F j).matrix * star (U : Matrix _ _ ℂ))‖ ≤
      ‖output F Ω‖ := by
  classical
  let Q : PositiveFilter q (X j) :=
    ⟨(U : Matrix _ _ ℂ) * (F j).matrix * star (U : Matrix _ _ ℂ),
      (F j).positive.mul_mul_conjTranspose_same _⟩
  let G : FilterFamily q m X := Function.update F j Q
  have hG : Admissible a G := by
    intro k
    by_cases hk : k = j
    · subst k
      change tracePower (Function.update F j Q j) (2 / a j) = 1
      rw [Function.update_self]
      exact (Spectral.tracePower_conjugate (F j).positive U (2 / a j)).trans (hF.1 j)
    · simpa [G, Function.update_of_ne hk] using hF.1 k
  have he : output G Ω = insertionMap F Ω j Q.matrix := by
    change matrixOutput (fun k => liftLocal (X k) (G k).matrix) Ω =
      matrixOutput (Function.update (fun k => liftLocal (X k) (F k).matrix) j
        (liftLocal (X j) Q.matrix)) Ω
    congr 1
    funext k
    by_cases hk : k = j
    · subst k; simp [G]
    · simp [G, hk]
  rw [← he]
  exact hF.2 G hG

theorem IsMaximizer.local_unitary_stationarity {L q m : ℕ}
    {X : Fin m → Finset (Vertex L)} {a : Fin m → ℝ} {Ω : State L q}
    {F : FilterFamily q m X} (hF : IsMaximizer Ω a F) (j : Fin m)
    (B : Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ)
    (hB : star B = -B) :
    (inner ℂ (output F Ω)
      (insertionMap F Ω j (B * (F j).matrix - (F j).matrix * B))).re = 0 := by
  let : NormedAlgebra ℚ (Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  let C := (insertionMap F Ω j).toContinuousLinearMap
  let y (t : ℝ) := C (NormedSpace.exp (t • B) * (F j).matrix * star (NormedSpace.exp (t • B)))
  have hy : HasDerivAt y (C (B * (F j).matrix - (F j).matrix * B)) 0 := by
    have hd := (C.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (Stationarity.deriv_conjugation_matrix (F j).matrix B hB)
    convert hd using 1 <;> rfl
  have hzero : y 0 = output F Ω := by
    simp only [y, zero_smul, NormedSpace.exp_zero, one_mul, star_one, mul_one]
    exact insertionMap_self F Ω j
  have hh : ∀ t, ‖y t‖ ≤ ‖y 0‖ := by
    intro t
    rw [hzero]
    have hU : NormedSpace.exp (t • B) ∈ unitary _ := by
      apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      rw [skewAdjoint.mem_iff]
      simp [hB]
    exact hF.insertion_unitary_max j ⟨_, hU⟩
  have hs := Stationarity.re_inner_deriv_eq_zero_of_max hy hh
  rw [hzero] at hs
  exact hs

end PolynomialPEPS.PinnedEntropy.NestedFilter

namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped Matrix.Norms.L2Operator MatrixOrder

lemma trace_strip_local {L q : ℕ} (v : State L q) (X : Finset (Vertex L))
    (F : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (hF : IsUnit F.det) (hc : Commute F (reducedDensity v X))
    (C : Operator L q) (hC : SupportedOn C X) :
    inner ℂ v (asMap (liftLocal X F * C * liftLocal X F⁻¹) v) = inner ℂ v (asMap C v) := by
  obtain ⟨B, rfl⟩ := hC
  rw [← liftLocal_mul, ← liftLocal_mul, inner_asMap_liftLocal, inner_asMap_liftLocal]
  rw [Matrix.trace_mul_comm (F * B * F⁻¹) (reducedDensity v X)]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hc.eq]
  rw [Matrix.mul_assoc F (reducedDensity v X) B,
    Matrix.mul_assoc F (reducedDensity v X * B) F⁻¹, Matrix.trace_mul_comm F]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul F hF, Matrix.mul_one]
  exact Matrix.trace_mul_comm _ _

def propagateConjugation {L q : ℕ} : {m : ℕ} →
    (Fin m → Operator L q) → (Fin m → Operator L q) → Operator L q → Operator L q
  | 0, _, _, C => C
  | _ + 1, T, I, C => propagateConjugation (fun j => T j.succ) (fun j => I j.succ)
      (T 0 * C * I 0)

lemma matrixOutput_propagate {L q m : ℕ} (T I : Fin m → Operator L q)
    (hI : ∀ j, I j * T j = 1) (C : Operator L q) (v : State L q) :
    matrixOutput T (asMap C v) =
      asMap (propagateConjugation T I C) (matrixOutput T v) := by
  induction m generalizing C v with
  | zero => rfl
  | succ m ih =>
    rw [matrixOutput_succ, matrixOutput_succ]
    have he : asMap (T 0) (asMap C v) =
        asMap (T 0 * C * I 0) (asMap (T 0) v) := by
      rw [← asMap_mul, ← asMap_mul]
      have hp : (T 0 * C * I 0) * T 0 = T 0 * C := by
        simp only [Matrix.mul_assoc, hI 0, Matrix.mul_one]
      rw [hp]
    rw [he]
    exact ih _ _ (fun j => hI j.succ) _ _

lemma propagate_trace_strip {L q m : ℕ} (v : State L q)
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (F : FilterFamily q m X) (hdet : ∀ j, IsUnit (F j).matrix.det)
    (hc : ∀ j, Commute (F j).matrix (reducedDensity v (X j)))
    (C : Operator L q) (hC : ∀ j, SupportedOn C (X j)) :
    inner ℂ v (asMap (propagateConjugation
      (fun j => liftLocal (X j) (F j).matrix)
      (fun j => liftLocal (X j) (F j).matrix⁻¹) C) v) = inner ℂ v (asMap C v) := by
  induction m generalizing C with
  | zero => rfl
  | succ m ih =>
    rw [propagateConjugation]
    have hs (j : Fin m) : SupportedOn
        (liftLocal (X 0) (F 0).matrix * C * liftLocal (X 0) (F 0).matrix⁻¹)
        (X j.succ) := by
      have hh : X 0 ⊆ X j.succ := hX (Fin.zero_le _)
      exact ((SupportedOn.mul (SupportedOn.mul
        (⟨_, rfl⟩ : SupportedOn (liftLocal (X 0) (F 0).matrix) (X 0)) (hC 0))
        (⟨_, rfl⟩ : SupportedOn (liftLocal (X 0) (F 0).matrix⁻¹) (X 0)))).mono hh
    rw [ih (fun j => X j.succ) (fun _ _ h => hX (Fin.succ_le_succ_iff.mpr h))
      (fun j => F j.succ) (fun j => hdet j.succ) (fun j => hc j.succ) _ hs]
    exact trace_strip_local v (X 0) (F 0).matrix (hdet 0) (hc 0) C (hC 0)

lemma output_succ {L q m : ℕ} {X : Fin (m+1) → Finset (Vertex L)}
    (F : FilterFamily q (m+1) X) (v : State L q) :
    output F v = output (fun j : Fin m => F j.succ)
      (asMap (liftLocal (X 0) (F 0).matrix) v) :=
  matrixOutput_succ _ _

lemma insertionMap_succ_zero {L q m : ℕ} {X : Fin (m+1) → Finset (Vertex L)}
    (F : FilterFamily q (m+1) X) (v : State L q)
    (B : Matrix (RegionConfiguration q (X 0)) (RegionConfiguration q (X 0)) ℂ) :
    insertionMap F v 0 B = matrixOutput (fun j : Fin m => liftLocal (X j.succ) (F j.succ).matrix)
      (asMap (liftLocal (X 0) B) v) := by
  change matrixOutput (Function.update _ 0 _) v = _
  simp only [matrixOutput_succ, Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _)]
  rfl

lemma insertionMap_succ_succ {L q m : ℕ} {X : Fin (m+1) → Finset (Vertex L)}
    (F : FilterFamily q (m+1) X) (v : State L q) (j : Fin m)
    (B : Matrix (RegionConfiguration q (X j.succ)) (RegionConfiguration q (X j.succ)) ℂ) :
    insertionMap F v j.succ B = insertionMap (fun k : Fin m => F k.succ)
      (asMap (liftLocal (X 0) (F 0).matrix) v) j B := by
  change matrixOutput (Function.update _ j.succ _) v = matrixOutput (Function.update _ j _) _
  rw [matrixOutput_succ]
  simp only [Function.update_of_ne (Fin.succ_ne_zero j).symm]
  congr 1
  funext k
  by_cases hk : k = j
  · subst k; simp
  · simp [Function.update_of_ne hk,
      Function.update_of_ne (fun h => hk (Fin.succ_inj.mp h))]

theorem commute_of_insertion_stationarity {L q m : ℕ}
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (F : FilterFamily q m X) (Ω : State L q)
    (hdet : ∀ j, IsUnit (F j).matrix.det)
    (hstat : ∀ j (B : Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ),
      star B = -B → (inner ℂ (output F Ω)
        (insertionMap F Ω j (B * (F j).matrix - (F j).matrix * B))).re = 0) :
    ∀ j, Commute (F j).matrix (reducedDensity (output F Ω) (X j)) := by
  induction m generalizing Ω with
  | zero => intro j; exact Fin.elim0 j
  | succ m ih =>
    have htail : ∀ j : Fin m, Commute (F j.succ).matrix
        (reducedDensity (output F Ω) (X j.succ)) := by
      rw [output_succ]
      apply ih (fun j => X j.succ) (fun _ _ h => hX (Fin.succ_le_succ_iff.mpr h))
        (fun j => F j.succ) _ (fun j => hdet j.succ)
      intro j B hB
      simpa only [output_succ, insertionMap_succ_succ] using hstat j.succ B hB
    intro j
    refine Fin.cases ?_ (fun k => htail k) j
    apply Stationarity.commute_of_unitary_trace_stationarity
      (reducedDensity_isHermitian _ _) (F 0).positive (hdet 0)
    intro B hB
    let C := liftLocal (X 0) (B - (F 0).matrix * B * (F 0).matrix⁻¹)
    have hCj (k : Fin m) : SupportedOn C (X k.succ) :=
      SupportedOn.mono (⟨_, rfl⟩ : SupportedOn C (X 0)) (hX (Fin.zero_le _))
    have hrel : liftLocal (X 0) (B * (F 0).matrix - (F 0).matrix * B) =
        C * liftLocal (X 0) (F 0).matrix := by
      rw [← liftLocal_mul]
      congr 1
      simp only [Matrix.sub_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul (F 0).matrix (hdet 0), Matrix.mul_one]
    have hh := hstat 0 B hB
    rw [insertionMap_succ_zero, hrel, asMap_mul, matrixOutput_propagate
      _ (fun k : Fin m => liftLocal (X k.succ) (F k.succ).matrix⁻¹)] at hh
    · have ho : matrixOutput (fun k : Fin m => liftLocal (X k.succ) (F k.succ).matrix)
          (asMap (liftLocal (X 0) (F 0).matrix) Ω) = output F Ω := (output_succ F Ω).symm
      rw [ho] at hh
      rw [propagate_trace_strip (output F Ω) (fun k => X k.succ)
        (fun _ _ h => hX (Fin.succ_le_succ_iff.mpr h)) (fun k => F k.succ)
        (fun k => hdet k.succ) htail C hCj] at hh
      rw [inner_asMap_liftLocal] at hh
      rw [Matrix.trace_mul_comm]
      exact hh
    · intro k
      rw [← liftLocal_mul, Matrix.nonsing_inv_mul (F k.succ).matrix (hdet k.succ), liftLocal_one]

theorem IsMaximizer.local_commute_of_invertible {L q m : ℕ}
    {X : Fin m → Finset (Vertex L)} (hX : Monotone X)
    {F : FilterFamily q m X} {Ω : State L q} {a : Fin m → ℝ}
    (hF : IsMaximizer Ω a F) (hdet : ∀ j, IsUnit (F j).matrix.det) :
    ∀ j, Commute (F j).matrix (reducedDensity (output F Ω) (X j)) :=
  commute_of_insertion_stationarity X hX F Ω hdet hF.local_unitary_stationarity

end PolynomialPEPS.PinnedEntropy.NestedFilter

end

end OAI
