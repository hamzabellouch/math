import Mathlib
import OAI.Analysis.Commutator.LittleGrothendieckSequence
import OAI.Analysis.Commutator.MatrixVectorTrace
import OAI.Analysis.Commutator.MatrixFreeSymmetry
import OAI.Analysis.Commutator.NormalCopiesAverage

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
lemma commutator_perturbation_unitball (Y Z A : K →L[ℂ] K) {b e : ℝ}
    (hb : ‖Z*A-A*Z‖ ≤ b) (he : ‖Y-Z‖ ≤ e) (hA : ‖A‖ ≤ 1) :
    ‖Y*A-A*Y‖ ≤ b+2*e := by
  have hid : Y*A-A*Y=(Z*A-A*Z)+((Y-Z)*A-A*(Y-Z)) := by
    simp only [sub_mul,mul_sub]; abel
  rw [hid]
  have hn : 0 ≤ e := (norm_nonneg _).trans he
  calc
    _ ≤ ‖Z*A-A*Z‖+‖(Y-Z)*A-A*(Y-Z)‖ := norm_add_le _ _
    _ ≤ b+2*‖Y-Z‖*‖A‖ := add_le_add hb (operator_commutator_norm_le _ _)
    _ ≤ b+2*e := by nlinarith [norm_nonneg (Y-Z),norm_nonneg A]

private lemma commutator_perturbation_starHom
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (g : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Y Z : A) (s : unitary B) {b e : ℝ}
    (hb : ‖f Z*g (s:B)-g (s:B)*f Z‖ ≤ b) (he : ‖Z-Y‖ ≤ e) :
    ‖f Y*g (s:B)-g (s:B)*f Y‖ ≤ b+2*e := by
  apply commutator_perturbation_unitball (f Y) (f Z) (g (s:B)) hb
  · rw [← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le f (Y-Z)).trans
      (by simpa only [norm_sub_rev] using he)
  · exact (NonUnitalStarAlgHom.norm_apply_le g (s:B)).trans
      (LittleGrothendieck.unitary_norm_le_one s)

namespace MatrixTower

open OperatorAmplification TracialSequence

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι)

local instance finiteSquareConditionalBoundDecidableEq : DecidableEq ι := Classical.decEq ι

variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=ι) τ) ω
  (matrixVonNeumann ι i₀ (generated M E))
  (matrixInclusion ι i₀ M (generated M E) (generated_le M E)))

omit [Nonempty ι] in
include hnormal in
private theorem square_original_copies_average
    (hE : Monotone (fun n => (E n).hom.range))
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    {δ : ℝ} (hδ : 0≤δ)
    (hY : ∀ a : M, ‖Y*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖≤δ*‖a‖) :
    ∃ Z : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι,
      ‖Z‖≤‖Y‖ ∧ ‖Z-Y‖≤δ ∧
      (∀ a : M, (a:H →L[ℂ] H)∈generated M E →
        Z*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)=
        diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Z) ∧
      (∀ a : M, ‖Z*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
        diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Z‖≤(3*δ)*‖a‖) := by
  exact original_copies_average (H:=H) M E τ hnormal ι hE Y hδ hY

include hnormal hω F in
theorem square_symmetry_after_average
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hY : ∀ a : M,‖Y*diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)-
      diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)*Y‖ ≤ δ*‖a‖)
    (s : unitary (CStarMatrix ι ι M)) (hs0 : MatrixGNS.trace (ι:=ι) τ (s:CStarMatrix ι ι M)=0)
    (hs2 : (s:CStarMatrix ι ι M)*(s:CStarMatrix ι ι M)=1) :
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι Y*MatrixGNS.representation τ (s:CStarMatrix ι ι M)-
      MatrixGNS.representation τ (s:CStarMatrix ι ι M)*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι Y‖ ≤ 3122*δ := by
  have havg := square_original_copies_average ι M E τ hnormal hE Y hδ hY
  obtain ⟨Z, _, hd, hZQ, hZ⟩ := havg
  have symmetry := matrix_free_symmetry_bound (H := H) ι i₀ M
  have atGenerated := symmetry (generated M E) (generated_le M E) τ
  have atFilter := atGenerated ω hω
  change _ at *
  delta finiteSquareConditionalBoundDecidableEq matrixFreeSymmetryDecidableEq at *
  have inFreePosition := atFilter F
  have inFactor := inFreePosition (generated_factor M E hirr) hτ hfaith h1
  have forAverage := inFactor Z
  have hs := forAverage (fun q => hZQ _ q.property) (mul_nonneg (by norm_num) hδ) hZ s hs0 hs2
  have h := commutator_perturbation_starHom
    (diagonal (H:=SumSpace (H:=τ.GNS) ι) ι)
    (MatrixGNS.representation (ι:=ι) τ) Y Z s hs hd
  convert h using 1; ring

end MatrixTower

end Kadison

end

end OAI
