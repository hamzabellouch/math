import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.QuotientSurjective
import OAI.Analysis.JiangSu.CentralSequences.SmallTraceNormUltrapower
import OAI.Analysis.JiangSu.Nonunital.ScalarStrictComparison

namespace OAI

section

noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain DirectComparison Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem projection_gap_tracial_ultrapower [Nonempty (NormalizedTrace A)]
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : StrictComparison hcone) (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ)≤atTop)
    (e f : lp (fun _ : ℕ => A) ∞)
    (he : ∀ n,0≤e n) (hen : ∀ n,‖e n‖≤1)
    (hf : ∀ n,0≤f n) (hfn : ∀ n,‖f n‖≤1)
    (c : ℝ) (hc : 0<c)
    (hede : ∀ r : ℝ,0<r → ∀ᶠ n in (U : Filter ℕ),
      ∀ τ : NormalizedTrace A,(τ.functional (e n-e n*e n)).re<r)
    (hgap : ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,
      (τ.functional (e n)).re+c≤(τ.functional (f n)).re)
    (hfde : ∀ r : ℝ,0<r → ∀ᶠ n in (U : Filter ℕ),
      ∀ τ : NormalizedTrace A,(τ.functional (f n-f n*f n)).re<r) :
    ∃ s : FamilyUltrapower (fun τ : NormalizedTrace A => τ.unitized) U,
      star s*s=(familyNullIdeal (fun τ : NormalizedTrace A => τ.unitized) (U : Filter ℕ)).quotientStarHom (boundedInr (A := A) e) ∧
      (familyNullIdeal (fun τ : NormalizedTrace A => τ.unitized) (U : Filter ℕ)).quotientStarHom (boundedInr (A := A) f)*s=s := by
  classical
  let d : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hd (n : ℕ) : 0<d n := by dsimp [d]; positivity
  have hd1 (n : ℕ) : d n≤1 := by
    dsimp [d]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hd0 : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P : ℕ → ℕ → Prop := fun m n =>
    (∀ τ : NormalizedTrace A,(τ.functional (e n-e n*e n)).re<d m*c/3) ∧
    (∀ τ : NormalizedTrace A,(τ.functional (e n)).re+c≤(τ.functional (f n)).re) ∧
    (∀ τ : NormalizedTrace A,(τ.functional (f n-f n*f n)).re<d m*c/3)
  have hP (m : ℕ) : ∀ᶠ n in (U : Filter ℕ),P m n := by
    exact (hede _ (by positivity)).and (hgap.and (hfde _ (by positivity)))
  obtain ⟨j,hj,hjP⟩ := isometry_diagonal_choice U hfree P hP
  have hlocal (n : ℕ) (hn : P (j n) n) :
      ∃ s : Unitization ℂ A,‖s‖≤2 ∧ ‖star s*s-Unitization.inr (e n)‖<2*d (j n) ∧ ‖Unitization.inr (f n)*s-s‖≤2*d (j n) := by
    obtain ⟨s,hs,hse,hsf⟩ := projection_gap_isometry_inr hcone hcmp (e n) (f n)
      (he n) (hen n) (hf n) (hfn n) (d (j n)) (d (j n)) c (d (j n))
      (hd _) (hd _) (hd1 _) hc (hd _) (hd1 _) hn.2.1 hn.1 hn.2.2
    exact ⟨s,hs,by linarith,hsf⟩
  let s : ℕ → Unitization ℂ A := fun n => if hn : P (j n) n then (hlocal n hn).choose else 0
  have hsn (n : ℕ) : ‖s n‖≤2 := by
    dsimp [s]
    split_ifs with hn
    · exact (hlocal n hn).choose_spec.1
    · simp
  let b : lp (fun _ : ℕ => Unitization ℂ A) ∞ := ⟨s,memℓp_infty ⟨2,by
    rintro _ ⟨n,rfl⟩
    exact hsn n⟩⟩
  have hse : Tendsto (fun n => ‖star (b n)*b n-Unitization.inr (e n)‖) (U : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_
      (by simpa using (tendsto_const_nhds (x := (2:ℝ))).mul (hd0.comp hj))
    filter_upwards [hjP] with n hn
    change ‖star (s n)*s n-Unitization.inr (e n)‖≤2*d (j n)
    simp only [s,dite_eq_left hn]
    exact (hlocal n hn).choose_spec.2.1.le
  have hsf : Tendsto (fun n => ‖Unitization.inr (f n)*b n-b n‖) (U : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_
      (by simpa using (tendsto_const_nhds (x := (2:ℝ))).mul (hd0.comp hj))
    filter_upwards [hjP] with n hn
    change ‖Unitization.inr (f n)*s n-s n‖≤2*d (j n)
    simp only [s,dite_eq_left hn]
    exact (hlocal n hn).choose_spec.2.2
  let T := fun τ : NormalizedTrace A => τ.unitized
  let q := (familyNullIdeal T (U : Filter ℕ)).quotientStarHom
  refine ⟨q b,?_,?_⟩
  · have hz : q (star b*b-boundedInr (A := A) e)=0 := by
      apply (familyQuotientMap_eq_zero T U _).mpr
      exact squeeze_zero (fun n => familyTwoNorm_nonneg T _) (fun n => familyTwoNorm_le_norm T _) hse
    simpa only [map_sub,map_mul,map_star,sub_eq_zero] using hz
  · have hz : q (boundedInr (A := A) f*b-b)=0 := by
      apply (familyQuotientMap_eq_zero T U _).mpr
      exact squeeze_zero (fun n => familyTwoNorm_nonneg T _) (fun n => familyTwoNorm_le_norm T _) hsf
    simpa only [map_sub,map_mul,sub_eq_zero] using hz

end NonunitalGamma

end
end

end OAI
