import OAI.Analysis.FactorGeneration.EnergyDescent
import OAI.Analysis.FactorGeneration.Expectations
import OAI.Analysis.FactorGeneration.MatrixAlgebras
import OAI.Analysis.FactorGeneration.UniformPartitions

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/
namespace Tracial
open scoped BigOperators

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_normal_matrix_approximation
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (x : M.toStarSubalgebra) [IsStarNormal x] (ε : ℝ) (hε : 0 < ε) :
    ∃ k n : ℕ,n=2^k ∧ ∃ E : MatrixUnitSystem (Fin n) M.toStarSubalgebra,
      ∃ c : Fin n → ℂ,τ.norm₂ (x-∑ j,c j • E.entry j j) < ε := by
  obtain ⟨Q,c,hc⟩ := exists_normal_spectral_approximation x (ε/2) (by positivity)
  obtain ⟨k,R,hn,ht,d,hd⟩ := exists_dyadic_spectral_sum_approximation τ hdiff Q
    (fun _ : Unit => c) (ε/2) (by positivity)
  obtain ⟨E,hdiag,hstar,hmul,hsum⟩ := exists_matrixUnits_for_partition τ hfactor R
    (by rw [hn]; positivity) (fun i j => (ht i).trans (ht j).symm)
  let F : MatrixUnitSystem (Fin R.size) M.toStarSubalgebra := ⟨E,hstar,hmul,hsum⟩
  refine ⟨k,R.size,hn,F,d (),?_⟩
  change τ.norm₂ (x-∑ j,d () j • E j j) < ε
  simp only [hdiag]
  have he : x-∑ j,d () j • (R.piece j).val =
      (x-∑ i,c i • (Q.piece i).val)+
      ((∑ i,c i • (Q.piece i).val)-∑ j,d () j • (R.piece j).val) := by abel
  rw [he]
  exact (τ.norm₂_add_le _ _).trans_lt (by
    have h₁ := (τ.norm₂_le_norm _).trans_lt hc
    have h₂ := hd ()
    linarith)

end

/-! A constructed full matrix algebra reduces the actual relative-commutant
expectation energy by a uniform factor for a centered nonzero element. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N D M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem commutator_norm₂_bound (a b : M.toStarSubalgebra) :
    τ.norm₂ (a*b-b*a) ≤ 2*‖a‖*τ.norm₂ b := by
  have h := norm_sub_le (baseVector τ (a*b)) (baseVector τ (b*a))
  change τ.norm₂ (a*b-b*a) ≤ τ.norm₂ (a*b)+τ.norm₂ (b*a) at h
  have hl := τ.norm₂_mul_le a b
  have hr := τ.norm₂_mul_le_right b a
  nlinarith

theorem commutator_norm₂_approximation (u v x z : M.toStarSubalgebra)
    (hc : v*z=z*v) :
    τ.norm₂ (u*x-x*u) ≤ 2*‖u‖*τ.norm₂ (x-z)+2*‖z‖*τ.norm₂ (u-v) := by
  have he : u*x-x*u=(u*(x-z)-(x-z)*u)- (z*(u-v)-(u-v)*z) := by
    simp only [mul_sub,sub_mul]
    rw [hc]
    abel
  rw [he]
  have h := norm_sub_le (baseVector τ (u*(x-z)-(x-z)*u))
    (baseVector τ (z*(u-v)-(u-v)*z))
  change τ.norm₂ ((u*(x-z)-(x-z)*u)-(z*(u-v)-(u-v)*z)) ≤
    τ.norm₂ (u*(x-z)-(x-z)*u)+τ.norm₂ (z*(u-v)-(u-v)*z) at h
  exact h.trans (add_le_add (commutator_norm₂_bound τ u (x-z))
    (commutator_norm₂_bound τ z (u-v)))

theorem expectation_energy_descent_of_unitary_approximation (hDM : D ≤ M)
    (u : unitary M.toStarSubalgebra) (v x : M.toStarSubalgebra)
    (hd : τ.norm₂ x ≤ τ.norm₂ (conjugateLinear u x-x))
    (hclose : τ.norm₂ ((u : M.toStarSubalgebra)-v) <
      τ.norm₂ x/(4*(‖x‖+1)))
    (hc : ∀ z : M.toStarSubalgebra,z.val ∈ D → v*z=z*v) :
    τ.norm₂ (conditionalExpectation τ hDM x)^2 ≤ (15/16 : ℝ)*τ.norm₂ x^2 := by
  let z := conditionalExpectation τ hDM x
  have hcomm := commutator_norm₂_approximation τ (u : M.toStarSubalgebra) v x z
    (hc z (conditionalExpectation_mem τ hDM x))
  have hdisp := displacement_le_commutator τ u x
  have hu := unitary_norm_le (u : M.toStarSubalgebra) u.property.1
  have hz := conditionalExpectation_norm_le τ hDM x
  have hn : 0 ≤ τ.norm₂ (x-z) := norm_nonneg _
  have hδ : 0 ≤ τ.norm₂ ((u : M.toStarSubalgebra)-v) := norm_nonneg _
  have hsmall : 4*(‖x‖+1)*τ.norm₂ ((u : M.toStarSubalgebra)-v) < τ.norm₂ x := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4*(‖x‖+1))).mp hclose
    nlinarith
  have hr : τ.norm₂ x/4 ≤ τ.norm₂ (x-z) := by
    have h₁ := mul_le_mul_of_nonneg_right hu hn
    have h₂ := mul_le_mul_of_nonneg_right hz hδ
    nlinarith
  have hpy := conditionalExpectation_pythagoras τ hDM x
  change τ.norm₂ z^2+τ.norm₂ (x-z)^2=τ.norm₂ x^2 at hpy
  nlinarith [sq_nonneg (τ.norm₂ (x-z)-τ.norm₂ x/4),
    show 0 ≤ τ.norm₂ x from norm_nonneg _]

theorem exists_irreducible_matrix_energy_descent (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : x ≠ 0) (ht : τ.trace x=0) :
    ∃ k n : ℕ,n=2^k ∧ ∃ E : MatrixUnitSystem (Fin n) N.toStarSubalgebra,
      τ.norm₂ (conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤
        (15/16 : ℝ)*τ.norm₂ x^2 := by
  let P := insideAlgebra (M := M) (P := N)
  obtain ⟨u,hu⟩ := exists_strict_centered_displacement τ P (by
    intro c hc
    exact hirr c (fun a => hc ⟨coordinateInclusion hNM a,a.property⟩)) x hx ht
  let a : N.toStarSubalgebra := ⟨(u.val : M.toStarSubalgebra).val,u.property⟩
  let : IsStarNormal a := ⟨by
    apply Subtype.ext
    exact congrArg (fun b : M.toStarSubalgebra => b.val)
      (u.val.property.1.trans u.val.property.2.symm)⟩
  have hxpos : 0 < τ.norm₂ x := lt_of_le_of_ne (norm_nonneg _)
    (fun h => hx ((τ.norm₂_eq_zero_iff x).mp h.symm))
  obtain ⟨k,n,hn,E,c,hc⟩ := exists_normal_matrix_approximation (restrictedTrace τ hNM)
    hfactor hdiff a (τ.norm₂ x/(4*(‖x‖+1))) (by positivity)
  let F := E.map (coordinateInclusion hNM)
  let v : M.toStarSubalgebra := ∑ j,c j • F.entry j j
  refine ⟨k,n,hn,E,expectation_energy_descent_of_unitary_approximation τ
    F.relativeVonNeumann_le u.val v x hu.le ?_ ?_⟩
  · change τ.norm₂ (coordinateInclusion hNM (a-∑ j,c j • E.entry j j)) < _ at hc
    rw [map_sub,map_sum] at hc
    simp only [map_smul] at hc
    exact hc
  · intro z hz
    have hz' := ((F.relativeStar_mem z.val).mp hz).2
    change (∑ j,c j • F.entry j j)*z=z*(∑ j,c j • F.entry j j)
    simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun b : M.toStarSubalgebra => c j • b) (Subtype.ext (hz' j j))

end Tracial

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/
section
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {D P M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_restricted (hPM : P ≤ M) (hDP : D ≤ P)
    (x : P.toStarSubalgebra) :
    conditionalExpectation τ (hDP.trans hPM) (coordinateInclusion hPM x)=
      coordinateInclusion hPM (conditionalExpectation (restrictedTrace τ hPM) hDP x) := by
  apply conditionalExpectation_eq_of_orthogonal τ (hDP.trans hPM)
  · exact conditionalExpectation_mem (restrictedTrace τ hPM) hDP x
  · intro a
    let b : insideAlgebra (M := P) (P := D) := ⟨⟨a.val.val,hDP a.property⟩,a.property⟩
    exact conditionalExpectation_orthogonal (restrictedTrace τ hPM) hDP x b

end Tracial
namespace MatrixUnitSystem
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem relative_antitone (E : MatrixUnitSystem ι M.toStarSubalgebra)
    (F : MatrixUnitSystem κ M.toStarSubalgebra) (h : E.algebra ≤ F.algebra) :
    F.relativeVonNeumann ≤ E.relativeVonNeumann := by
  intro x hx
  have hx' := (F.relativeStar_mem x).mp hx
  apply (E.relativeStar_mem x).mpr
  refine ⟨hx'.1,?_⟩
  let y : M.toStarSubalgebra := ⟨x,hx'.1⟩
  have hF : ∀ i j,Commute (F.entry i j) y := fun i j => Subtype.ext (hx'.2 i j)
  intro i j
  exact congrArg Subtype.val (((F.commute_algebra_iff y).mpr hF) _ (h (E.entry_mem i j))).eq

/-- The product commutant is exactly the commutant of the new system inside
of the old commutant, with both algebras represented on the same H. -/
theorem relative_product_inside (E : MatrixUnitSystem ι M.toStarSubalgebra)
    (F : MatrixUnitSystem κ E.relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ i j k l,Commute (E.entry i j)
      ((F.map (coordinateInclusion E.relativeVonNeumann_le)).entry k l)) :
    (E.product (F.map (coordinateInclusion E.relativeVonNeumann_le)) hc).relativeVonNeumann =
      F.relativeVonNeumann := by
  let G := F.map (coordinateInclusion E.relativeVonNeumann_le)
  apply le_antisymm
  · intro x hx
    have hE := E.relative_antitone (E.product G hc) (E.algebra_le_product_left G hc) hx
    have hG := G.relative_antitone (E.product G hc) (E.algebra_le_product_right G hc) hx
    exact (F.relativeStar_mem x).mpr ⟨hE,((G.relativeStar_mem x).mp hG).2⟩
  · intro x hx
    have hF := (F.relativeStar_mem x).mp hx
    have hE := (E.relativeStar_mem x).mp hF.1
    apply ((E.product G hc).relativeStar_mem x).mpr
    refine ⟨hE.1,?_⟩
    intro a b
    change ((E.entry a.1 b.1).val*(F.entry a.2 b.2).val)*x=
      x*((E.entry a.1 b.1).val*(F.entry a.2 b.2).val)
    rw [mul_assoc,hF.2,← mul_assoc,hE.2,mul_assoc]

end MatrixUnitSystem

end

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_compatible_matrix_energy_descent (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (E : MatrixUnitSystem ι N.toStarSubalgebra) (o : ι)
    (x : M.toStarSubalgebra) (ht : τ.trace x=0)
    (hy : conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x ≠ 0) :
    ∃ k n : ℕ,n=2^k ∧ ∃ F : MatrixUnitSystem (Fin n) N.toStarSubalgebra,
      ∃ hc : ∀ i j l m,Commute (E.entry i j) (F.entry l m),
        E.algebra ≤ (E.product F hc).algebra ∧
        τ.norm₂ (conditionalExpectation τ
          ((E.product F hc).map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤
          (15/16 : ℝ)*τ.norm₂
            (conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 := by
  let EM := E.map (coordinateInclusion hNM)
  let C := EM.relativeVonNeumann
  let hCM := EM.relativeVonNeumann_le
  let y := conditionalExpectation τ hCM x
  let yC : C.toStarSubalgebra := ⟨y.val,conditionalExpectation_mem τ hCM x⟩
  let τC := restrictedTrace τ hCM
  have hyC : yC ≠ 0 := by
    intro h
    apply hy
    exact Subtype.ext (congrArg (fun b : C.toStarSubalgebra => b.val) h)
  have htC : τC.trace yC=0 := (conditionalExpectation_trace τ hCM x).trans ht
  obtain ⟨k,n,hn,G,hG⟩ := exists_irreducible_matrix_energy_descent τC
    (E.relative_inclusion hNM) (E.relative_scalar_center o hfactor)
    (E.relative_diffuse o hdiff) (E.relative_irreducible hNM o hirr) yC hyC htC
  let F := G.map (coordinateInclusion E.relativeVonNeumann_le)
  have hc : ∀ i j l m,Commute (E.entry i j) (F.entry l m) := by
    intro i j l m
    apply Subtype.ext
    exact ((E.relativeStar_mem (G.entry l m).val).mp (G.entry l m).property).2 i j
  let GM := G.map (coordinateInclusion (E.relative_inclusion hNM))
  have hcM : ∀ i j l m,Commute (EM.entry i j)
      ((GM.map (coordinateInclusion hCM)).entry l m) := by
    intro i j l m
    apply Subtype.ext
    exact congrArg (fun b : N.toStarSubalgebra => b.val) (hc i j l m).eq
  have hproduct : ((E.product F hc).map (coordinateInclusion hNM)).relativeVonNeumann =
      GM.relativeVonNeumann := by
    convert EM.relative_product_inside GM hcM using 1
    rfl
  let hDC := GM.relativeVonNeumann_le
  have he : conditionalExpectation τ (hDC.trans hCM) x =
      coordinateInclusion hCM (conditionalExpectation τC hDC yC) := by
    rw [← conditionalExpectation_tower τ (hDC.trans hCM) hCM hDC x]
    exact conditionalExpectation_restricted τ hCM hDC yC
  refine ⟨k,n,hn,F,hc,E.algebra_le_product_left F hc,?_⟩
  have hnorm : τ.norm₂ (conditionalExpectation τ (hDC.trans hCM) x)^2 ≤
      (15/16 : ℝ)*τ.norm₂ y^2 := by
    rw [he]
    exact hG
  simpa only [hproduct] using hnorm

end Tracial

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def reindex (E : MatrixUnitSystem ι A) (e : κ ≃ ι) : MatrixUnitSystem κ A where
  entry i j := E.entry (e i) (e j)
  star_entry i j := E.star_entry _ _
  mul_entry i j k l := by simpa only [e.apply_eq_iff_eq] using E.mul_entry (e i) (e j) (e k) (e l)
  total := (e.sum_comp (fun i => E.entry i i)).trans E.total

theorem reindex_algebra (E : MatrixUnitSystem ι A) (e : κ ≃ ι) :
    (E.reindex e).algebra=E.algebra := by
  apply le_antisymm
  · exact ((E.reindex e).algebra_le_iff _).mpr (fun i j => E.entry_mem _ _)
  · apply (E.algebra_le_iff _).mpr
    intro i j
    simpa only [reindex,Equiv.apply_symm_apply] using
      (E.reindex e).entry_mem (e.symm i) (e.symm j)

open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem map_algebra_mono (E : MatrixUnitSystem ι N.toStarSubalgebra)
    (F : MatrixUnitSystem κ N.toStarSubalgebra) (h : E.algebra ≤ F.algebra)
    (f : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra) :
    (E.map f).algebra ≤ (F.map f).algebra := by
  apply ((E.map f).algebra_le_iff _).mpr
  intro i j
  obtain ⟨a,ha⟩ := (F.mem_algebra (E.entry i j)).mp (h (E.entry_mem i j))
  change f (E.entry i j) ∈ (F.map f).algebra
  rw [← ha]
  simp only [map_sum,map_smul]
  exact (F.map f).algebra.sum_mem fun k _ =>
    (F.map f).algebra.sum_mem fun l _ => (F.map f).algebra.smul_mem ((F.map f).entry_mem k l) _

theorem mapped_reindex_relative (E : MatrixUnitSystem ι N.toStarSubalgebra)
    (e : κ ≃ ι) (f : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra) :
    ((E.reindex e).map f).relativeVonNeumann=(E.map f).relativeVonNeumann := by
  apply le_antisymm
  · exact (E.map f).relative_antitone _ (E.map_algebra_mono _ (E.reindex_algebra e).ge f)
  · exact ((E.reindex e).map f).relative_antitone _ ((E.reindex e).map_algebra_mono _
      (E.reindex_algebra e).le f)

end MatrixUnitSystem

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_commuting_matrix_extension
    (τ : TracialRepresentation M) (E : MatrixUnitSystem ι M.toStarSubalgebra) (o : ι)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (n : ℕ) (hn : 0 < n) :
    ∃ F : MatrixUnitSystem (Fin n) M.toStarSubalgebra,
      ∃ hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l),
        Function.Injective F.hom ∧
        (∀ j,τ.trace (F.entry j j)=(((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
        E.algebra ≤ (E.product F hc).algebra ∧
        WOTClosed (E.product F hc).concreteAlgebra := by
  let C := E.relativeVonNeumann
  let τC := restrictedTrace τ E.relativeVonNeumann_le
  obtain ⟨Q,hsize,ht⟩ := exists_uniform_trace_partition τC (E.relative_diffuse o hdiff)
    n (identityProjection C) (n : ℝ)⁻¹ (inv_nonneg.mpr (Nat.cast_nonneg n)) (by
      change τC.trace 1=(n : ℂ)*(((n : ℝ)⁻¹ : ℝ) : ℂ)
      simp [τC.trace_one,hn.ne'])
  subst n
  obtain ⟨G,hdiag,hG,hGM,hGW⟩ := exists_matrixAlgebra_for_unit_partition τC
    (E.relative_scalar_center o hfactor) Q hn (fun i j => (ht i).trans (ht j).symm)
  let f := coordinateInclusion E.relativeVonNeumann_le
  let F := G.map f
  have hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l) := by
    intro i j k l
    apply Subtype.ext
    exact ((E.relativeStar_mem (G.entry k l).val).mp (G.entry k l).property).2 i j
  refine ⟨F,hc,?_,?_,E.algebra_le_product_left F hc,
    (E.product F hc).concreteAlgebra_wotClosed⟩
  · intro a b hab
    apply hG
    have hm (a : Matrix (Fin Q.size) (Fin Q.size) ℂ) : F.hom a=f (G.hom a) := by
      simp only [MatrixUnitSystem.hom_apply,map_sum,map_smul]
      rfl
    rw [hm,hm] at hab
    exact (StarSubalgebra.inclusion_injective E.relativeVonNeumann_le) hab
  · intro j
    change τC.trace (G.entry j j)=_
    rw [hdiag]
    exact ht j

end Tracial

end Generator

end

end OAI
