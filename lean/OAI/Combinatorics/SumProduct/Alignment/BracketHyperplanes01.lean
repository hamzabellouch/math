import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.LeibmanSquare01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open Polynomial Finset
open scoped BigOperators
end
end
 

 
section

 

open MeasureTheory Filter
open scoped ENNReal

namespace PolynomialNullSet
variable {R : Type*} [CommRing R] [IsDomain R]
  [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R]

theorem ae_eval_ne_zero : ∀ {n : ℕ} (p : MvPolynomial (Fin n) R) (_hp : p ≠ 0)
    (μ : Fin n → Measure R) [∀ i, SigmaFinite (μ i)] [∀ i, NullSingletonClass (μ i)],
    ∀ᵐ x ∂Measure.pi μ, MvPolynomial.eval x p ≠ 0
  | 0, p, hp, μ, _, _ => by
    rw [p.eq_C_of_isEmpty] at *
    simp only [MvPolynomial.eval_C]
    exact Filter.Eventually.of_forall fun _ => MvPolynomial.C_ne_zero.mp hp
  | n+1, p, hp, μ, _, _ => by
    classical
    let p' := MvPolynomial.finSuccEquiv R n p
    have hp' : p' ≠ 0 := EmbeddingLike.map_ne_zero_iff.mpr hp
    have hl : p'.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp'
    have ih := ae_eval_ne_zero p'.leadingCoeff hl (fun j => μ j.succ)
    have hfiber : ∀ᵐ y ∂Measure.pi (fun j : Fin n => μ j.succ),
        ∀ᵐ z ∂μ 0, MvPolynomial.eval (Fin.cons z y) p ≠ 0 := by
      filter_upwards [ih] with y hy
      have hmap : p'.map (MvPolynomial.eval y) ≠ 0 := by
        intro hh
        apply hy
        have hc := congrArg (fun q : Polynomial R => q.coeff p'.natDegree) hh
        simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
          Polynomial.leadingCoeff] using hc
      have hz := (Polynomial.finite_setOfPred_isRoot hmap).countable.ae_notMem (μ 0)
      simpa only [Set.mem_ofPred_eq, Polynomial.IsRoot,
        MvPolynomial.eval_eq_eval_mv_eval', p'] using hz
    have hm : MeasurableSet {x : R × (Fin n → R) |
        MvPolynomial.eval (Fin.cons x.1 x.2) p ≠ 0} := by
      apply MeasurableSet.compl
      exact isClosed_eq (p.continuous_eval.comp (by fun_prop)) continuous_const |>.measurableSet
    have hprod : ∀ᵐ x ∂(μ 0).prod (Measure.pi fun j : Fin n => μ j.succ),
        MvPolynomial.eval (Fin.cons x.1 x.2) p ≠ 0 :=
      (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm hm).mpr hfiber)
    have hpres := measurePreserving_piFinSuccAbove μ 0
    have hpull := hpres.quasiMeasurePreserving.tendsto_ae.eventually
      (show ∀ᵐ x ∂(μ 0).prod (Measure.pi fun j : Fin n => μ ((0 : Fin (n+1)).succAbove j)),
        MvPolynomial.eval (Fin.cons x.1 x.2) p ≠ 0 by simpa using hprod)
    simpa only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
      Fin.succAbove_zero, Fin.removeNth_zero, Fin.cons_self_tail] using hpull

theorem measure_zero {n : ℕ} (p : MvPolynomial (Fin n) R) (hp : p ≠ 0)
    (μ : Fin n → Measure R) [∀ i, SigmaFinite (μ i)] [∀ i, NullSingletonClass (μ i)] :
    Measure.pi μ {x | MvPolynomial.eval x p = 0} = 0 := by
  simpa only [ae_iff, not_not] using ae_eval_ne_zero p hp μ
end PolynomialNullSet

namespace BracketHyperplanes
open MeasureTheory Set
open scoped BigOperators
noncomputable section

variable {d : ℕ}
def torusMap (x : Fin d → ℝ) : UnitAddTorus (Fin d) := fun i => (x i : UnitAddCircle)
lemma continuous_torusMap : Continuous (torusMap (d := d)) := by
  unfold torusMap
  fun_prop

def linearPolynomial (a : Fin d → ℝ) (b : ℝ) : MvPolynomial (Fin d) ℝ :=
  (∑ i, MvPolynomial.C (a i) * MvPolynomial.X i) - MvPolynomial.C b

@[simp] lemma eval_linearPolynomial (a x : Fin d → ℝ) (b : ℝ) :
    MvPolynomial.eval x (linearPolynomial a b) = (∑ i, a i*x i)-b := by
  simp [linearPolynomial]

lemma linearPolynomial_ne_zero (a : Fin d → ℝ) (ha : a ≠ 0) (b : ℝ) :
    linearPolynomial a b ≠ 0 := by
  intro he
  have hzero := congrArg (MvPolynomial.eval (0 : Fin d → ℝ)) he
  have hb : b=0 := by
    rw [eval_linearPolynomial, MvPolynomial.eval_zero] at hzero
    simpa using hzero
  subst b
  apply ha
  funext i
  have hi := congrArg (MvPolynomial.eval (Pi.single i 1)) he
  simpa [Pi.single_apply] using hi

lemma measure_affine_slice_zero (a : Fin d → ℝ) (ha : a ≠ 0) (b : ℝ)
    (μ : Fin d → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    [∀ i, NullSingletonClass (μ i)] :
    Measure.pi μ {x | ∑ i, a i*x i = b} = 0 := by
  simpa only [eval_linearPolynomial,sub_eq_zero] using
    PolynomialNullSet.measure_zero (linearPolynomial a b) (linearPolynomial_ne_zero a ha b) μ

 

theorem torus_image_affine_slice_null (a : Fin d → ℝ) (ha : a ≠ 0)
    (b : ℝ) (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    volume (torusMap '' (K ∩ {x | ∑ i, a i*x i = b})) = 0 := by
  classical
  let μ : Fin d → Measure ℝ := fun _ => volume.restrict (Ioc (0:ℝ) 1)
  have hm : MeasurePreserving (torusMap (d := d)) (Measure.pi μ) volume := by
    convert! measurePreserving_pi
      (fun _ : Fin d => volume.restrict (Ioc (0:ℝ) 1)) (fun _ => volume)
      (fun _ => by simpa using AddCircle.measurePreserving_mk 1 0) using 1
  have hs : IsClosed {x : Fin d → ℝ | ∑ i, a i*x i = b} :=
    isClosed_eq (by fun_prop) continuous_const
  have hcompact := (hK.inter_right hs).image continuous_torusMap
  rw [← hm.measure_preimage hcompact.isClosed.measurableSet.nullMeasurableSet]
  have hsub : torusMap ⁻¹' (torusMap '' (K ∩ {x | ∑ i, a i*x i = b})) ⊆
      ⋃ k : Fin d → ℤ, {x | ∑ i, a i*x i = b - ∑ i, a i*(k i:ℝ)} := by
    rintro x ⟨y,hy,heq⟩
    have hz (i : Fin d) : ∃ k : ℤ, (k:ℝ) = y i-x i := by
      have hh := congrFun heq i
      change ((y i:ℝ):UnitAddCircle) = ((x i:ℝ):UnitAddCircle) at hh
      have hh' : ((y i-x i : ℝ) : UnitAddCircle) = 0 := by
        simpa only [AddCircle.coe_sub,sub_eq_zero] using hh
      obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).mp hh'
      exact ⟨k,by simpa using hk⟩
    choose k hk using hz
    apply Set.mem_iUnion.mpr
    refine ⟨k,?_⟩
    have he (i : Fin d) : y i = x i+(k i:ℝ) := by linarith [hk i]
    have hsum := hy.2
    change ∑ i, a i*y i = b at hsum
    simp_rw [he,mul_add,Finset.sum_add_distrib] at hsum
    exact eq_sub_iff_add_eq.mpr hsum
  apply measure_mono_null hsub
  exact measure_iUnion_null fun k => measure_affine_slice_zero a ha _ μ

end
end BracketHyperplanes

 

namespace CompactNullFamilies
open MeasureTheory Set Topology Filter
noncomputable section

variable {P Y X : Type*} [TopologicalSpace P] [CompactSpace P] [T2Space P]
  [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

 

omit [T2Space Y] in
theorem finite_majorants (q : C(Y,X)) (v : C(P × Y,ℝ))
    (hzero : ∀ p : P, μ (q '' {y | v (p,y) = 0}) = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ tests : Finset C(X,ℝ), ∃ ε : ℝ, 0 < ε ∧
      (∀ f ∈ tests, (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∫ x, f x ∂μ) < δ) ∧
      ∀ p : P, ∃ f ∈ tests, ∀ y : Y, 0 ≤ v (p,y) → v (p,y) ≤ ε →
        (1:ℝ)/2 < f (q y) := by
  classical
  have hp (p : P) : ∃ f : C(X,ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∫ x, f x ∂μ) < δ ∧ ∀ y, v (p,y)=0 → f (q y)=1 := by
    let K := q '' {y | v (p,y)=0}
    have hK : IsCompact K :=
      (isClosed_eq (v.continuous.comp (continuous_const.prodMk continuous_id))
        continuous_const).isCompact.image q.continuous
    obtain ⟨U,hKU,hU,hμU⟩ := hK.exists_isOpen_lt_of_lt (ENNReal.ofReal δ)
      (by rw [hzero p]; exact ENNReal.ofReal_pos.mpr hδ)
    obtain ⟨f,hfK,hfU,hfs,hf⟩ := exists_continuous_one_zero_of_isCompact hK
      hU.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKU)
    refine ⟨f,hf,?_,fun y hy => hfK ⟨y,hy,rfl⟩⟩
    have hi := (integral_le_measure (fun x _ => (hf x).2)
      (fun x hx => (hfU hx).le)).trans_lt hμU
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp hi
  choose f hf hi hfzero using hp
  let W : Set ((P × ℝ) × X) :=
    (fun t : P × Y => ((t.1,v t),q t.2)) '' Set.univ
  have hW : IsCompact W := isCompact_univ.image (by
    exact (continuous_fst.prodMk v.continuous).prodMk
      (q.continuous.comp continuous_snd))
  let B (p : P) : Set (P × ℝ) := Prod.fst ''
    (W ∩ {z | f p z.2 ≤ (1:ℝ)/2})
  have hB (p : P) : IsClosed (B p) :=
    ((hW.inter_right (isClosed_le ((f p).continuous.comp continuous_snd)
      continuous_const)).image continuous_fst).isClosed
  have hpB (p : P) : (p,0) ∉ B p := by
    rintro ⟨⟨⟨p',r⟩,x⟩,⟨⟨⟨a,y⟩,_,he⟩,hfx⟩,hfirst⟩
    have hpa : a=p := by exact (congrArg (fun z => z.1.1) he).trans (congrArg Prod.fst hfirst)
    have hr : v (a,y)=0 := by exact (congrArg (fun z => z.1.2) he).trans (congrArg Prod.snd hfirst)
    have hx : q y=x := congrArg Prod.snd he
    subst a
    change f p x ≤ (1:ℝ)/2 at hfx
    rw [← hx,hfzero p y hr] at hfx
    norm_num at hfx
  have hopper (p : P) : ∃ U : Set P, ∃ V : Set ℝ,
      IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ 0 ∈ V ∧ U ×ˢ V ⊆ (B p)ᶜ :=
    isOpen_prod_iff.mp (hB p).isOpen_compl p 0 (hpB p)
  choose U V hU hV hpU hzV hUV using hopper
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun p _ => Set.mem_iUnion.mpr ⟨p,hpU p⟩)
  have hVnhds : (⋂ p ∈ S, V p) ∈ 𝓝 (0:ℝ) := by
    exact (Filter.biInter_mem S.finite_toSet).mpr (fun p hp => (hV p).mem_nhds (hzV p))
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hVnhds
  refine ⟨S.image f,ε/2,by positivity,?_,?_⟩
  · intro g hg
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hg
    exact ⟨hf p,hi p⟩
  · intro p
    obtain ⟨a,ha,hpa⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ p))
    refine ⟨f a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,?_⟩
    intro y hv0 hve
    have hball : v (p,y) ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hv0]
      linarith
    have hvV : v (p,y) ∈ V a := Set.mem_iInter₂.mp (hεV hball) a ha
    have hout : (p,v (p,y)) ∉ B a := hUV a ⟨hpa,hvV⟩
    apply lt_of_not_ge
    intro hle
    apply hout
    exact ⟨((p,v (p,y)),q y),⟨⟨(p,y),Set.mem_univ _,rfl⟩,hle⟩,rfl⟩

end
end CompactNullFamilies

namespace BracketHyperplanes
open MeasureTheory Set
open scoped BigOperators
noncomputable section
variable {d : ℕ}

 
theorem torus_image_mod_affine_null (a : Fin d → ℝ) (ha : a ≠ 0)
    (b : ℝ) (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    volume (torusMap '' (K ∩ {x | ‖((∑ i, a i*x i - b : ℝ) : UnitAddCircle)‖ = 0})) = 0 := by
  have hs : torusMap '' (K ∩ {x | ‖((∑ i, a i*x i-b : ℝ) : UnitAddCircle)‖ = 0}) ⊆
      ⋃ k : ℤ, torusMap '' (K ∩ {x | ∑ i, a i*x i = b+(k:ℝ)}) := by
    rintro t ⟨x,⟨hx,hzero⟩,rfl⟩
    obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).mp (norm_eq_zero.mp hzero)
    have hk' : (k:ℝ) = ∑ i, a i*x i-b := by simpa using hk
    exact Set.mem_iUnion.mpr ⟨k,x,⟨hx,by change ∑ i, a i*x i = b+(k:ℝ); linarith only [hk']⟩,rfl⟩
  exact measure_mono_null hs (measure_iUnion_null fun k =>
    torus_image_affine_slice_null a ha _ K hK)

 

theorem compact_bracket_tests {P : Type*} [TopologicalSpace P]
    [CompactSpace P] [T2Space P]
    (a : C(P, Fin d → ℝ)) (ha : ∀ p, a p ≠ 0) (b : C(P, ℝ))
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ tests : Finset C(UnitAddTorus (Fin d),ℝ), ∃ ε : ℝ, 0 < ε ∧
      (∀ f ∈ tests, (∀ t, 0 ≤ f t ∧ f t ≤ 1) ∧ (∫ t, f t) < δ) ∧
      ∀ p : P, ∃ f ∈ tests, ∀ x ∈ K,
        ‖((∑ i, a p i*x i-b p : ℝ) : UnitAddCircle)‖ ≤ ε →
        (1:ℝ)/2 < f (torusMap x) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let q : C(K,UnitAddTorus (Fin d)) :=
    ⟨fun x => torusMap x.val, continuous_torusMap.comp continuous_subtype_val⟩
  let v : C(P × K,ℝ) := ⟨fun t =>
      ‖((∑ i, a t.1 i*t.2.val i-b t.1 : ℝ) : UnitAddCircle)‖, by
        apply Continuous.norm
        apply (AddCircle.continuous_mk' 1).comp
        exact (continuous_finsetSum Finset.univ (fun i _ =>
          ((continuous_apply i).comp (a.continuous.comp continuous_fst)).mul
            ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))).sub
          (b.continuous.comp continuous_fst)⟩
  have hzero (p : P) : volume (q '' {y | v (p,y)=0}) = 0 := by
    apply measure_mono_null (μ := volume) _ (torus_image_mod_affine_null (a p) (ha p) (b p) K hK)
    rintro t ⟨y,hy,rfl⟩
    exact ⟨y.val,⟨y.property,hy⟩,rfl⟩
  obtain ⟨T,ε,hε,hT,hcover⟩ := CompactNullFamilies.finite_majorants volume q v hzero δ hδ
  refine ⟨T,ε,hε,hT,?_⟩
  intro p
  obtain ⟨f,hf,hfcover⟩ := hcover p
  exact ⟨f,hf,fun x hx hsmall => hfcover ⟨x,hx⟩ (norm_nonneg (((∑ i, a p i*x i-b p : ℝ) : UnitAddCircle))) hsmall⟩

end
end BracketHyperplanes

 

end
end
end
end

end OAI
