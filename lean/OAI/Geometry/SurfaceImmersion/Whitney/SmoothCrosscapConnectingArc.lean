import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapEndArcs
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothInteriorDoubleArc
import OAI.Geometry.SurfaceImmersion.Whitney.PairArcJoin
import OAI.Geometry.SurfaceImmersion.Whitney.UnitIntervalArcImages

namespace OAI

/-! Assemble the two actual crosscap endpoint pieces and the compact
interior into one smooth regular embedded ordered connecting arc. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem smooth_crosscap_connecting_arc_endpoint_regular
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ S : SmoothCompactArc (planeModel.prod planeModel) (M × M),
      S.curve '' Icc S.start S.finish = range Γ ∧
      S.curve S.start = (p,p) ∧ S.curve S.finish = (q,q) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (S.curve t).1) S.start) ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (S.curve t).1) S.finish) := by
  obtain ⟨a,b,P,Q,ha,hab,hb,hPi,hQi,hP0,hQ1,hPa,hQb,hPg,hQg,hPreg,hQreg⟩ :=
    crosscap_end_arcs_regular cp cq hΓ hinj hzero hone heq hne
  let ua : I := ⟨a,⟨ha.le,(hab.trans hb).le⟩⟩
  let ub : I := ⟨b,⟨(ha.trans hab).le,hb.le⟩⟩
  obtain ⟨T,hTi,hTa,hTb⟩ := smooth_interior_double_arc hf hreg hΓ hinj heq hne ha hab hb
  let C : ℝ → M × M := Γ ∘ projIcc 0 1 zero_le_one
  have hCv (u : I) : C (u:ℝ) = Γ u := by
    change Γ (projIcc 0 1 zero_le_one u) = Γ u
    rw [projIcc_val]
  have hCi : (Icc (0:ℝ) 1).InjOn C := unitInterval_extension_injective hinj
  have hPiC : P.curve '' Icc P.start P.finish = C '' Icc 0 a := by
    rw [hPi,unitInterval_extension_image (Γ := Γ) (a := 0) (b := a) le_rfl (hab.trans hb).le]
    congr 1
    ext u
    simp only [mem_ofPred_eq]
    exact ⟨fun h => ⟨u.property.1,h⟩,fun h => h.2⟩
  have hQiC : Q.curve '' Icc Q.start Q.finish = C '' Icc b 1 := by
    rw [hQi,unitInterval_extension_image (Γ := Γ) (a := b) (b := 1) (ha.trans hab).le le_rfl]
    congr 1
    ext u
    simp only [mem_ofPred_eq]
    exact ⟨fun h => ⟨h,u.property.2⟩,fun h => h.1⟩
  have hTiC : T.arc.curve '' Icc T.arc.start T.arc.finish = C '' Icc a b := by
    rw [unitInterval_extension_image (Γ := Γ) ha.le hb.le]
    exact hTi
  have hTstart : T.arc.curve T.arc.start = C a := hTa.trans (hCv ua).symm
  have hTfinish : T.arc.curve T.arc.finish = C b := hTb.trans (hCv ub).symm
  have hTgood (t : ℝ) : T.arc.curve t ∈ surfaceDoublePairs f := by
    rw [T.curve_eq]
    exact (T.lift t).property
  let pa : surfaceDoublePairs f := ⟨Γ ua,hne ua ha (hab.trans hb),heq ua⟩
  have hpaP : pa.val = P.curve P.finish := (hPa ua rfl).symm
  have hpaT : pa.val = T.arc.curve T.arc.start := hTa.symm
  have hcrossPT := ordered_arc_images_separated ha.le hab.le
    (hCi.mono (Icc_subset_Icc le_rfl hb.le)) P T.arc hPiC hTiC hTstart
  obtain ⟨J,e,_,_,_,hJs,_,hJi,hJ0,hJ1,hJleft,hJgerm⟩ := join_pair_arcs hf hreg P T.arc pa hpaP hpaT hPg
    (Filter.Eventually.of_forall hTgood) hcrossPT
  have hJiC : J.curve '' Icc J.start J.finish = C '' Icc 0 b := by
    rw [hJi,hPiC,hTiC,← Set.image_union,Icc_union_Icc_eq_Icc ha.le hab.le]
  have hJgood : ∀ᶠ t in 𝓝 J.finish, J.curve t ∈ surfaceDoublePairs f := by
    filter_upwards [hJgerm] with t ht
    rw [ht]
    exact hTgood (e t)
  have hQstart : Q.curve Q.start = C b := (hQb ub rfl).trans (hCv ub).symm
  let pb : surfaceDoublePairs f := ⟨Γ ub,hne ub (ha.trans hab) hb,heq ub⟩
  have hpbJ : pb.val = J.curve J.finish := by
    exact (hJ1.trans hTb).symm
  have hpbQ : pb.val = Q.curve Q.start := (hQb ub rfl).symm
  have hcrossJQ := ordered_arc_images_separated (ha.trans hab).le hb.le hCi J Q hJiC hQiC hQstart
  obtain ⟨S,eS,heSs,heSi,_,hSs,hSf,hSi,hS0,hS1,hSleft,hSright⟩ := join_pair_arcs hf hreg J Q pb hpbJ hpbQ hJgood hQg hcrossJQ
  refine ⟨S,?_,hS0.trans (hJ0.trans hP0),hS1.trans hQ1,?_,?_⟩
  · rw [hSi,hJiC,hQiC,← Set.image_union,Icc_union_Icc_eq_Icc (ha.trans hab).le hb.le,
      unitInterval_extension_image (Γ := Γ) (a := 0) (b := 1) le_rfl le_rfl]
    have hset : {t : I | (0:ℝ) ≤ t ∧ (t:ℝ) ≤ 1} = univ := by
      ext t
      simp only [mem_ofPred_eq,mem_univ,iff_true]
      exact t.property
    rw [hset,image_univ]
  · have hstart : S.start = P.start := hSs.trans hJs
    have hg : S.curve =ᶠ[𝓝 P.start] P.curve := by
      rw [hstart] at hSleft
      rw [hJs] at hJleft
      exact hSleft.trans hJleft
    rw [hstart]
    have hPs := P.smooth.contMDiffAt (P.domain_open.mem_nhds
      (P.interval_subset (left_mem_Icc.mpr P.start_lt_finish.le)))
    exact regular_curve_germ (contMDiffAt_fst.comp _ hPs) (hg.fun_comp Prod.fst) hPreg
  · have heEnd : eS S.finish = Q.finish := by rw [hSf,eS.apply_symm_apply]
    have hQs := contMDiffAt_fst.comp Q.finish (Q.smooth.contMDiffAt (Q.domain_open.mem_nhds
      (Q.interval_subset (right_mem_Icc.mpr Q.start_lt_finish.le))))
    have hQr := regular_curve_reparameterization eS heSs heSi
      (by rw [heEnd]; exact hQs) (by rw [heEnd]; exact hQreg)
    have hQat : ContMDiffAt 𝓘(ℝ) planeModel ∞ (fun t => (Q.curve t).1) (eS S.finish) := by
      rw [heEnd]
      exact hQs
    exact regular_curve_germ (hQat.comp S.finish (heSs.contMDiff.contMDiffAt))
      (hSright.fun_comp Prod.fst) hQr

theorem smooth_crosscap_connecting_arc
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hinj : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ S : SmoothCompactArc (planeModel.prod planeModel) (M × M),
      S.curve '' Icc S.start S.finish = range Γ ∧
      S.curve S.start = (p,p) ∧ S.curve S.finish = (q,q) := by
  obtain ⟨S,hSi,hS0,hS1,_,_⟩ :=
    smooth_crosscap_connecting_arc_endpoint_regular hf hreg cp cq hΓ hinj hzero hone heq hne
  exact ⟨S,hSi,hS0,hS1⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
