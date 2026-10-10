import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSFilters.SpectralPowers

namespace OAI

/-! Ordered filter products and unitary phase absorption. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace PolynomialPEPS.PinnedEntropy
open scoped Matrix.Norms.L2Operator

lemma asMap_mul {L q : ℕ} (A B : Operator L q) (v : State L q) :
    asMap (A * B) v = asMap A (asMap B v) := by
  change (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) (A * B)) v = _
  rw [map_mul]
  rfl

lemma asMap_unitary {L q : ℕ} {U : Operator L q}
    (hU : U ∈ unitary _) : asMap U ∈ unitary (State L q →L[ℂ] State L q) := by
  constructor
  · change star (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) U) * Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) U = 1
    rw [← map_star, ← map_mul, hU.1, map_one]
  · change Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) U * star (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) U) = 1
    rw [← map_star, ← map_mul, hU.2, map_one]

lemma asMap_unitary_norm {L q : ℕ} {U : Operator L q}
    (hU : U ∈ unitary _) (v : State L q) : ‖asMap U v‖ = ‖v‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (asMap_unitary hU) v

namespace NestedFilter

lemma PositiveFilter.conjugate_exists {L q : ℕ} [NeZero q]
    {X : Finset (Vertex L)} (F : PositiveFilter q X) {U : Operator L q}
    (hU : SupportedOn U X) (hu : U ∈ unitary _) :
    ∃ G : PositiveFilter q X,
      liftLocal X G.matrix = U * liftLocal X F.matrix * star U ∧
      ∀ p, tracePower G p = tracePower F p := by
  obtain ⟨u, rfl⟩ := hU.unitary_rep hu
  refine ⟨⟨(u : Matrix _ _ ℂ) * F.matrix * star (u : Matrix _ _ ℂ),
    F.positive.mul_mul_conjTranspose_same _⟩, ?_, ?_⟩
  · simp only [liftLocal_mul, liftLocal_star]
  · intro p
    exact Spectral.tracePower_conjugate F.positive u p

def matrixOutput {L q m : ℕ} (A : Fin m → Operator L q) (v : State L q) : State L q :=
  (List.ofFn fun j => asMap (A j)).foldl (fun w T => T w) v

lemma matrixOutput_zero {L q : ℕ} (A : Fin 0 → Operator L q) (v : State L q) :
    matrixOutput A v = v := by simp [matrixOutput]

lemma matrixOutput_succ {L q m : ℕ} (A : Fin (m+1) → Operator L q) (v : State L q) :
    matrixOutput A v = matrixOutput (fun j => A j.succ) (asMap (A 0) v) := by
  simp only [matrixOutput, List.ofFn_succ, List.foldl_cons]

lemma matrixOutput_conjugate {L q m : ℕ} (A : Fin m → Operator L q)
    {U : Operator L q} (hu : U ∈ unitary _) (v : State L q) :
    matrixOutput A (asMap U v) =
      asMap U (matrixOutput (fun j => star U * A j * U) v) := by
  induction m generalizing v with
  | zero => simp only [matrixOutput_zero]
  | succ m ih =>
    rw [matrixOutput_succ, matrixOutput_succ]
    have he : asMap (A 0) (asMap U v) =
        asMap U (asMap (star U * A 0 * U) v) := by
      rw [← asMap_mul, ← asMap_mul]
      congr 1
      rw [← mul_assoc, ← mul_assoc, hu.2, one_mul]
    rw [he]
    exact ih (fun j => A j.succ) _

theorem phase_absorption {L q m : ℕ} [NeZero q]
    (X : Fin m → Finset (Vertex L)) (hX : Monotone X)
    (F : FilterFamily q m X) (U : Fin m → Operator L q)
    (hUs : ∀ j, SupportedOn (U j) (X j)) (hUu : ∀ j, U j ∈ unitary _)
    (v : State L q) :
    ∃ G : FilterFamily q m X,
      (∀ j p, tracePower (G j) p = tracePower (F j) p) ∧
      ‖matrixOutput (fun j => U j * liftLocal (X j) (F j).matrix) v‖ =
        ‖output G v‖ := by
  induction m generalizing v with
  | zero =>
    refine ⟨F, fun _ _ => rfl, ?_⟩
    simp only [matrixOutput, output, List.ofFn_zero, List.foldl_nil]
  | succ m ih =>
    have hu0 : star (U 0) ∈ unitary (Operator L q) := by
      constructor
      · simpa only [star_star] using (hUu 0).2
      · simpa only [star_star] using (hUu 0).1
    have hs0 (j : Fin m) : SupportedOn (star (U 0)) (X j.succ) :=
      ((hUs 0).mono (hX (Fin.zero_le _))).star
    choose F' hF' hFp using fun j : Fin m =>
      (F j.succ).conjugate_exists (hs0 j) hu0
    let U' : Fin m → Operator L q := fun j => star (U 0) * U j.succ * U 0
    have hU's (j : Fin m) : SupportedOn (U' j) (X j.succ) :=
      ((hs0 j).mul (hUs j.succ)).mul ((hUs 0).mono (hX (Fin.zero_le _)))
    have hU'u (j : Fin m) : U' j ∈ unitary _ :=
      (unitary _).mul_mem ((unitary _).mul_mem hu0 (hUu j.succ)) (hUu 0)
    have hX' : Monotone (fun j : Fin m => X j.succ) :=
      fun _ _ h => hX (Fin.succ_le_succ_iff.mpr h)
    obtain ⟨G', hGp, hG⟩ := ih (fun j => X j.succ) hX' F' U' hU's hU'u
      (asMap (liftLocal (X 0) (F 0).matrix) v)
    let G : FilterFamily q (m+1) X := Fin.cases (F 0) G'
    refine ⟨G, ?_, ?_⟩
    · intro j p
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · exact (hGp k p).trans (hFp k p)
    · rw [matrixOutput_succ, asMap_mul,
        matrixOutput_conjugate _ (hUu 0), asMap_unitary_norm (hUu 0)]
      have he : (fun j : Fin m => star (U 0) *
          (U j.succ * liftLocal (X j.succ) (F j.succ).matrix) * U 0) =
          (fun j => U' j * liftLocal (X j.succ) (F' j).matrix) := by
        funext j
        rw [hF' j, star_star]
        dsimp [U']
        simp only [mul_assoc]
        rw [← mul_assoc (U 0) (star (U 0)), (hUu 0).2, one_mul]
      rw [he, hG]
      simp only [output, G, List.ofFn_succ, List.foldl_cons, Fin.cases_zero, Fin.cases_succ]

end NestedFilter
end PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.PinnedEntropy.NestedFilter

theorem twisted_norm_le_maximizer {L q m : ℕ} [NeZero q]
    {X : Fin m → Finset (Vertex L)} (hX : Monotone X)
    {Ω : State L q} {a : Fin m → ℝ} {F : FilterFamily q m X}
    (hF : IsMaximizer Ω a F) (P : FilterFamily q m X) (hP : Admissible a P)
    (U : Fin m → Operator L q)
    (hUs : ∀ j, SupportedOn (U j) (X j)) (hUu : ∀ j, U j ∈ unitary _) :
    ‖matrixOutput (fun j => U j * liftLocal (X j) (P j).matrix) Ω‖ ≤ ‖output F Ω‖ := by
  obtain ⟨G, hG, hnorm⟩ := phase_absorption X hX P U hUs hUu Ω
  rw [hnorm]
  apply hF.2 G
  intro j
  exact (hG j (2 / a j)).trans (hP j)

end PolynomialPEPS.PinnedEntropy.NestedFilter

end

end OAI
