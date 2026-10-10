import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.FiniteMatrixModels
import OAI.Analysis.JiangSu.MatrixAlgebras.TracialMatrixModelExtraction

namespace OAI

noncomputable section


namespace DirectPacking
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] [Nonempty I] (T : I → TracialState A) (U : Ultrafilter ℕ)
local notation "D" => FamilyUltrapower T U
local notation "ι" => familyUltrapowerMap T U
local notation "J" => familyNullIdeal T (U : Filter ℕ)
local notation "q" => Pureness.ClosedStarIdeal.quotientStarHom (familyNullIdeal T (U : Filter ℕ))

lemma model_quotient_zero (x : lp (fun _ : ℕ => A) ∞) (δ : ℕ → ℝ)
    (hδ : Tendsto δ (U : Filter ℕ) (𝓝 0))
    (hx : ∀ᶠ k in (U : Filter ℕ),familyTwoNorm T (x k)≤δ k) : q x=0 := by
  apply (familyQuotientMap_eq_zero T U x).mpr
  exact squeeze_zero' (Eventually.of_forall (fun k => familyTwoNorm_nonneg _ _)) hx hδ

variable {m : ℕ} (K : ℕ → Finset (unitary A)) (δ : ℕ → ℝ)
  (v : (k : ℕ) → TracialMatrixModel T (StarAlgHom.id ℂ A) m (K k) (δ k))

def matrixModelEntry (i j : Fin m) : lp (fun _ : ℕ => A) ∞ :=
  ⟨fun k => (v k).entry i j,memℓp_infty_iff.mpr ⟨1,by
    rintro _ ⟨k,rfl⟩; exact (v k).norm_entry i j⟩⟩

omit [StarOrderedRing A] [Nontrivial A] [Nonempty I] in
@[simp] lemma matrixModelEntry_apply (i j : Fin m) (k : ℕ) :
    matrixModelEntry T K δ v i j k=(v k).entry i j := rfl

local notation "x" => matrixModelEntry T K δ v

lemma matrixModel_star (hδ : Tendsto δ (U : Filter ℕ) (𝓝 0)) (i j : Fin m) :
    star (q (x i j))=q (x j i) := by
  apply sub_eq_zero.mp
  rw [←map_star,←map_sub]
  apply model_quotient_zero T U _ δ hδ
  exact Eventually.of_forall fun k => ((v k).star_error i j).le

lemma matrixModel_mul (hδ : Tendsto δ (U : Filter ℕ) (𝓝 0)) (i j k l : Fin m) :
    q (x i j)*q (x k l)=if j=k then q (x i l) else 0 := by
  by_cases hjk : j=k
  · subst k
    simp only [ite_true]
    apply sub_eq_zero.mp
    rw [←map_mul,←map_sub]
    apply model_quotient_zero T U _ δ hδ
    apply Eventually.of_forall
    intro t
    change familyTwoNorm T ((v t).entry i j*(v t).entry j l-(v t).entry i l)≤δ t
    simpa only [ite_true] using ((v t).mul_error i j j l).le
  · simp only [hjk,ite_false]
    rw [←map_mul]
    apply model_quotient_zero T U _ δ hδ
    apply Eventually.of_forall
    intro t
    change familyTwoNorm T ((v t).entry i j*(v t).entry k l)≤δ t
    simpa only [hjk,ite_false,sub_zero] using ((v t).mul_error i j k l).le

lemma matrixModel_sum (hδ : Tendsto δ (U : Filter ℕ) (𝓝 0)) : ∑ i,q (x i i)=1 := by
  apply sub_eq_zero.mp
  rw [←map_sum,←map_one q,←map_sub]
  apply model_quotient_zero T U _ δ hδ
  apply Eventually.of_forall
  intro k
  simpa only [lp.coeFn_sub,Pi.sub_apply,lp.coeFn_sum,Finset.sum_apply,lp.infty_coeFn_one,Pi.one_apply,matrixModelEntry_apply]
    using (v k).unit_error.le

lemma matrixModel_commute (hδ : Tendsto δ (U : Filter ℕ) (𝓝 0))
    (i j : Fin m) (u : unitary A) (hu : ∀ᶠ k in (U : Filter ℕ),u∈K k) :
    Commute (q (x i j)) (ι (u:A)) := by
  apply commute_of_null_sequence T U (x i j) (u:A)
  apply squeeze_zero' (Eventually.of_forall (fun k => familyTwoNorm_nonneg _ _)) _ hδ
  filter_upwards [hu] with k hk
  exact ((v k).comm_error i j u hk).le

theorem central_matrix_of_tracial_models [TopologicalSpace.SeparableSpace A]
    (hfree : (U : Filter ℕ)≤atTop) (m : ℕ)
    (hmodel : ∀ (K : Finset (unitary A)) (ε : ℝ),0<ε →
      Nonempty (TracialMatrixModel T (StarAlgHom.id ℂ A) m K ε)) :
    ∃ η : CStarMatrix (Fin m) (Fin m) ℂ →⋆ₐ[ℂ] D,
      ∀ M (a : A),Commute (η M) (ι a) := by
  classical
  obtain ⟨u,hu⟩ := TopologicalSpace.exists_dense_seq (unitary A)
  let K (k : ℕ) : Finset (unitary A) := (Finset.range k).image u
  let δ (k : ℕ) : ℝ := 1/((k:ℝ)+1)
  have hδpos k : 0<δ k := by dsimp [δ]; positivity
  let v (k : ℕ) := Classical.choice (hmodel (K k) (δ k) (hδpos k))
  have hδ : Tendsto δ (U : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hfree
  let e : ConcreteMatrixUnits.System (Fin m) D :=
    ⟨fun i j => q (matrixModelEntry T K δ v i j),matrixModel_mul T U K δ v hδ,
      matrixModel_star T U K δ v hδ,matrixModel_sum T U K δ v hδ⟩
  refine ⟨e.hom,?_⟩
  intro M a
  apply e.hom_commute
  intro i j
  have hdense (n : ℕ) : Commute (e.entry i j) (ι (u n:A)) := by
    apply matrixModel_commute T U K δ v hδ
    have hev : ∀ᶠ k in (U : Filter ℕ),n<k := (eventually_gt_atTop n).filter_mono hfree
    filter_upwards [hev] with k hk
    exact Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr hk,rfl⟩
  have hι : Continuous (fun u : unitary A => ι (u:A)) := (map_continuous ι).comp continuous_subtype_val
  have he := hu.equalizer (continuous_const.mul hι) (hι.mul continuous_const) (funext fun n => (hdense n).eq)
  have hucomm (u : unitary A) : Commute (e.entry i j) (ι (u:A)) := congrFun he u
  obtain ⟨w,c,hw,_⟩ := CStarAlgebra.exists_sum_four_unitary a
  rw [hw,map_sum]
  apply Commute.sum_right
  intro l _
  rw [map_smul]
  exact (hucomm (w l)).smul_right (c l)

end DirectPacking


namespace DirectComparison
open Pureness CurrentMain DirectPacking Filter
open scoped ComplexOrder

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "T" => (fun τ : TracialState A => τ)
local notation "D" => FamilyUltrapower T U
local notation "ι" => familyUltrapowerMap T U

 theorem comparison_central_matrix (hfree : (U : Filter ℕ)≤atTop)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (hnuc : IsNuclear A)
    (m : ℕ) (hm : 0 < m) :
    ∃ η : CStarMatrix (Fin m) (Fin m) ℂ →⋆ₐ[ℂ] D,
      ∀ M (a : A),Commute (η M) (ι a) := by
  apply central_matrix_of_tracial_models T U hfree m
  intro K ε hε
  obtain ⟨v⟩ := comparison_finite_matrix_models U hfree hsimple hinf hcmp hnuc m hm K hε
  exact tracial_matrix_model_extract T U v

end DirectComparison

end

end OAI
