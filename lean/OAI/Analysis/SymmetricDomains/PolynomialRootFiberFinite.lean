import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Filter Set
open scoped Topology

theorem polynomial_analytic_sheets_nonmonic {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ))
    (a : Fin d → ℂ) (hlead : MvPolynomial.eval a P.leadingCoeff ≠ 0) (ha : (P.map (MvPolynomial.eval a)).Separable) :
    ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → ℂ) (W : Set (Fin d → ℂ)),
      I.card = P.natDegree ∧ IsOpen W ∧ a ∈ W ∧
      (∀ i, AnalyticOnNhd ℂ (g i) W) ∧ (∀ i, g i a = i.val) ∧
      ∀ y ∈ W, Function.Injective (fun i => g i y) ∧
        ∀ z : ℂ, Polynomial.eval₂ (MvPolynomial.eval y) z P = 0 ↔
          ∃ i, g i y = z := by
  classical
  have hne (y : Fin d → ℂ) (hy : MvPolynomial.eval y P.leadingCoeff ≠ 0) :
      P.map (MvPolynomial.eval y) ≠ 0 := by
    intro hz
    have H := congrArg (fun Q : Polynomial ℂ => Q.coeff P.natDegree) hz
    apply hy
    simpa only [Polynomial.coeff_map,Polynomial.coeff_natDegree,Polynomial.coeff_zero] using H
  let I : Finset ℂ := (P.map (MvPolynomial.eval a)).roots.toFinset
  have hcard : I.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots ha),
      IsAlgClosed.card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero hlead]
  have hi (i : I) : Polynomial.eval₂ (MvPolynomial.eval a) i.val P = 0 := by
    have h := Polynomial.mem_roots (hne a hlead) |>.mp
      (Multiset.mem_toFinset.mp i.property)
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using h
  have hs (i : I) : Polynomial.eval₂ (MvPolynomial.eval a) i.val P.derivative ≠ 0 := by
    simpa only [Polynomial.eval₂_id, Polynomial.eval₂_at_apply, Polynomial.derivative_map,
      Polynomial.eval_map] using
      ha.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := i.val)
        (by simpa only [Polynomial.eval₂_id, Polynomial.eval₂_at_apply, Polynomial.eval_map] using hi i)
  choose g hg hga hgr _hgu using fun i : I => polynomial_analytic_root P a i.val (hi i) (hs i)
  have hgi : ∀ᶠ y in 𝓝 a, Function.Injective (fun i => g i y) := by
    have hj : ∀ i j : I, ∀ᶠ y in 𝓝 a, i ≠ j → g i y ≠ g j y := by
      intro i j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
      · have hval : g i a ≠ g j a := by
          rw [hga, hga]
          exact fun h => hij (Subtype.ext h)
        exact ((hg i).continuousAt.ne_iff_eventually_ne (hg j).continuousAt).mp hval |>.mono
          (fun _ hh _ => hh)
    filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hj i))] with y hy
    intro i j hij
    by_contra h
    exact hy i j h hij
  have hall : ∀ᶠ y in 𝓝 a,
      (∀ i, AnalyticAt ℂ (g i) y) ∧
      (∀ i, Polynomial.eval₂ (MvPolynomial.eval y) (g i y) P = 0) ∧
      Function.Injective (fun i => g i y) := by
    exact (Filter.eventually_all.mpr (fun i => (hg i).eventually_analyticAt)).and
      ((Filter.eventually_all.mpr hgr).and hgi)
  have hle : ∀ᶠ y in 𝓝 a, MvPolynomial.eval y P.leadingCoeff ≠ 0 :=
    ((AnalyticOnNhd.eval_mvPolynomial P.leadingCoeff _ (mem_univ _)).continuousAt.ne_iff_eventually_ne continuousAt_const).mp hlead
  obtain ⟨W, hWsub, hW, haW⟩ := _root_.mem_nhds_iff.mp (hall.and hle)
  have hWlead : ∀ y ∈ W, MvPolynomial.eval y P.leadingCoeff ≠ 0 := fun y hy => (hWsub hy).2
  have hWsub := fun {y} (hy : y ∈ W) => (hWsub hy).1
  refine ⟨I, g, W, hcard, hW, haW, fun i y hy => (hWsub hy).1 i, hga, ?_⟩
  intro y hy
  have hyroot := (hWsub hy).2.1
  have hyinj := (hWsub hy).2.2
  refine ⟨hyinj, ?_⟩
  let J : Finset ℂ := Finset.univ.image (fun i : I => g i y)
  let K : Finset ℂ := (P.map (MvPolynomial.eval y)).roots.toFinset
  have hJK : J ⊆ K := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hne y (hWlead y hy))).mpr
      (by simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hyroot i))
  have hJcard : J.card = I.card := by
    rw [Finset.card_image_of_injective _ hyinj]
    simp
  have hKcard : K.card ≤ P.natDegree := by
    exact (Multiset.toFinset_card_le _).trans (le_of_eq
      (IsAlgClosed.card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero (hWlead y hy)))
  have hJKeq : J = K := Finset.eq_of_subset_of_card_le hJK (by rw [hJcard, hcard]; exact hKcard)
  intro z
  constructor
  · intro hz
    have hzK : z ∈ K := Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (hne y (hWlead y hy))).mpr
        (by simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hz))
    rw [← hJKeq] at hzK
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hzK
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact hyroot i

theorem relation_evenlyCovered_of_sheets {X Y J : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace J] [DiscreteTopology J] [Finite J]
    (R : Set (X × Y)) (a : X) (W : Set X) (hW : IsOpen W) (ha : a ∈ W)
    (g : J → X → Y) (hg : ∀ j, ContinuousOn (g j) W)
    (hi : ∀ x ∈ W, Function.Injective (fun j => g j x))
    (he : ∀ x ∈ W, ∀ y, (x,y) ∈ R ↔ ∃ j, g j x = y) :
    IsEvenlyCovered (fun r : R => r.val.1) a J := by
  classical
  let p : R → X := fun r => r.val.1
  let ψ : W × J → p ⁻¹' W := fun x =>
    ⟨⟨(x.1.val,g x.2 x.1.val),(he x.1.val x.1.property _).mpr ⟨x.2,rfl⟩⟩,x.1.property⟩
  have hψc : Continuous ψ := by
    apply continuous_prod_of_discrete_right.mpr
    intro j
    exact (continuous_subtype_val.prodMk (continuousOn_iff_continuous_domRestrict.mp (hg j))).subtype_mk _ |>.subtype_mk _
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have hx : x.1 = y.1 := Subtype.ext (congrArg (fun r : p ⁻¹' W => r.val.val.1) hxy)
    have hy : g x.2 x.1.val = g y.2 y.1.val := congrArg (fun r : p ⁻¹' W => r.val.val.2) hxy
    rw [← hx] at hy
    exact Prod.ext hx (hi _ x.1.property hy)
  have hψsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨j,hj⟩ := (he r.val.val.1 r.property r.val.val.2).mp r.val.property
    refine ⟨(⟨r.val.val.1,r.property⟩,j),?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl hj
  let π : p ⁻¹' W → W := fun r => ⟨r.val.val.1,r.property⟩
  have hπ : Continuous π :=
    (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  have hproper : IsProperMap ψ := isProperMap_of_comp_of_t2 hψc hπ isProperMap_fst_of_compactSpace
  let H : W × J ≃ₜ p ⁻¹' W :=
    (Equiv.ofBijective ψ ⟨hψinj,hψsurj⟩).toHomeomorphOfContinuousClosed hψc hproper.isClosedMap
  refine ⟨inferInstance,W,ha,hW,hW.preimage (continuous_fst.comp continuous_subtype_val),H.symm,?_⟩
  intro r
  have h := congrArg (fun t : p ⁻¹' W => t.val.val.1) (H.apply_symm_apply r)
  exact h

theorem polynomial_root_covering {d : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : X → (Fin d → ℂ))
    (hA : Continuous A) (hlead : ∀ x, MvPolynomial.eval (A x) P.leadingCoeff ≠ 0)
    (hsep : ∀ x, (P.map (MvPolynomial.eval (A x))).Separable) :
    IsCoveringMap (fun r : {r : X × ℂ | Polynomial.eval₂ (MvPolynomial.eval (A r.1)) r.2 P = 0} =>
      r.val.1) := by
  intro x
  obtain ⟨J,g,W,_,hWo,hxW,hg,_,hge⟩ := polynomial_analytic_sheets_nonmonic P (A x) (hlead x) (hsep x)
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := J)
  refine relation_evenlyCovered_of_sheets _ x (A ⁻¹' W) (hWo.preimage hA) hxW
    (fun j y => g j (A y)) ?_ ?_ ?_
  · intro j
    exact (hg j).continuousOn.comp hA.continuousOn (fun _ h => h)
  · intro y hy
    exact (hge (A y) hy).1
  · intro y hy z
    exact (hge (A y) hy).2 z

theorem continuous_polynomial_root_analyticAt {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : E → (Fin d → ℂ))
    (g : E → ℂ) (a : E) (hA : AnalyticAt ℂ A a) (hg : ContinuousAt g a)
    (hroot : ∀ᶠ x in 𝓝 a, Polynomial.eval₂ (MvPolynomial.eval (A x)) (g x) P = 0)
    (hsimple : Polynomial.eval₂ (MvPolynomial.eval (A a)) (g a) P.derivative ≠ 0) :
    AnalyticAt ℂ g a := by
  obtain ⟨b,hb,hba,_,hunique⟩ := polynomial_analytic_root P (A a) (g a)
    hroot.self_of_nhds hsimple
  have ht : Tendsto (fun x => (A x,g x)) (𝓝 a) (𝓝 (A a,g a)) := hA.continuousAt.prodMk hg
  have he : g =ᶠ[𝓝 a] fun x => b (A x) := by
    filter_upwards [ht hunique,hroot] with x hx hr
    exact hx hr
  exact (hb.comp hA).congr he.symm

theorem polynomial_root_fiber_finite {d : ℕ} {X : Type*}
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (A : X → (Fin d → ℂ))
    (x : X) (hlead : MvPolynomial.eval (A x) P.leadingCoeff ≠ 0) :
    ((fun r : {r : X × ℂ | Polynomial.eval₂ (MvPolynomial.eval (A r.1)) r.2 P = 0} =>
      r.val.1) ⁻¹' {x}).Finite := by
  have hne : P.map (MvPolynomial.eval (A x)) ≠ 0 := by
    intro hz
    apply hlead
    have H := congrArg (fun Q : Polynomial ℂ => Q.coeff P.natDegree) hz
    simpa only [Polynomial.coeff_map,Polynomial.coeff_natDegree,Polynomial.coeff_zero] using H
  apply Set.Finite.of_injOn (f := fun r => r.val.2) (t := {z | (P.map (MvPolynomial.eval (A x))).IsRoot z})
  · intro r hr
    change r.val.1 = x at hr
    change Polynomial.eval r.val.2 (P.map (MvPolynomial.eval (A x))) = 0
    rw [Polynomial.eval_map,← hr]
    exact r.property
  · intro r hr s hs hval
    apply Subtype.ext
    exact Prod.ext (hr.trans hs.symm) hval
  · exact Polynomial.finite_setOfPred_isRoot hne

end Release061

end

end OAI
