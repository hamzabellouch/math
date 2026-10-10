import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! Joint orbit laws from measure-preserving rotations and pointwise Haar
kernels. The proof avoids measurable eigenvector selections. -/
noncomputable section
open MeasureTheory
namespace InvariantIsing

lemma paired_map_eq_of_comp {G D : Type*} [MeasurableSpace G] [MeasurableSpace D]
    (H : Measure G) (d : D) (f Y : G → ℝ) (T : G → G)
    (hf : Measurable f) (hT : Measurable T) (hmap : H.map T=H)
    (hY : ∀ u, Y u=f (T u)) :
    H.map (fun u => (d,Y u))=H.map (fun u => (d,f u)) := by
  have he : (fun u => (d,Y u))=(fun u => (d,f u)) ∘ T := by
    funext u
    exact Prod.ext rfl (hY u)
  rw [he,← Measure.map_map (measurable_const.prodMk hf) hT,hmap]

lemma map_prod_eq_of_fiber_maps {X G E : Type*}
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace E]
    (P : Measure X) (H : Measure G) [SFinite P] [SFinite H]
    (f g : X × G → E) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ x, H.map (fun u => f (x,u))=H.map (fun u => g (x,u))) :
    (P.prod H).map f=(P.prod H).map g := by
  ext s hs
  rw [Measure.map_apply hf hs,Measure.map_apply hg hs,
    Measure.prod_apply (hf hs),Measure.prod_apply (hg hs)]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have hh := congrArg (fun Q : Measure E => Q s) (h x)
    have hfx : Measurable (fun u => f (x,u)) := hf.comp (measurable_const.prodMk measurable_id)
    have hgx : Measurable (fun u => g (x,u)) := hg.comp (measurable_const.prodMk measurable_id)
    rw [Measure.map_apply hfx hs,Measure.map_apply hgx hs] at hh
    exact hh

theorem invariant_joint_orbit_law {X G D : Type*}
    [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace D]
    (P : Measure X) [IsProbabilityMeasure P] (H : Measure G) [IsProbabilityMeasure H]
    (act : G → X → X) (hact : Measurable (Function.uncurry act))
    (hpres : ∀ u, P.map (act u)=P)
    (d : X → D) (Y : X → ℝ) (hd : Measurable d) (hY : Measurable Y)
    (hinv : ∀ u x, d (act u x)=d x)
    (orbit : D → G → ℝ) (horbit : Measurable (fun z : D × G => orbit z.1 z.2))
    (hkernel : ∀ x, H.map (fun u => (d x,Y (act u x)))=
      H.map (fun u => (d x,orbit (d x) u))) :
    P.map (fun x => (d x,Y x))=
      ((P.map d).prod H).map (fun z => (z.1,orbit z.1 z.2)) := by
  have hs := (MeasurePreserving.id H).skew_product hact
    (Filter.Eventually.of_forall hpres)
  have hp := ((show MeasurePreserving Prod.snd (H.prod P) P from measurePreserving_snd).comp hs).comp
    (show MeasurePreserving Prod.swap (P.prod H) (H.prod P) from Measure.measurePreserving_swap)
  have hf : Measurable (fun x => (d x,Y x)) := hd.prodMk hY
  have he := congrArg (fun Q : Measure X => Q.map (fun x => (d x,Y x))) hp.map_eq
  rw [Measure.map_map hf hp.measurable] at he
  have hF : Measurable (fun z : X × G => (d z.1,Y (act z.2 z.1))) :=
    (hd.comp measurable_fst).prodMk (hY.comp (hact.comp measurable_swap))
  have hB : Measurable (fun z : X × G => (d z.1,orbit (d z.1) z.2)) :=
    (hd.comp measurable_fst).prodMk
      (horbit.comp ((hd.comp measurable_fst).prodMk measurable_snd))
  have havg : P.map (fun x => (d x,Y x))=
      (P.prod H).map (fun z : X × G => (d z.1,Y (act z.2 z.1))) := by
    refine he.symm.trans ?_
    congr 1
    funext z
    exact Prod.ext (hinv z.2 z.1) rfl
  rw [havg,map_prod_eq_of_fiber_maps P H _ _ hF hB hkernel]
  have hdp : MeasurePreserving d P (P.map d) := ⟨hd,rfl⟩
  have hprod := hdp.prod (MeasurePreserving.id H)
  have ht := congrArg (fun Q : Measure (D × G) =>
    Q.map (fun z => (z.1,orbit z.1 z.2))) hprod.map_eq
  rw [Measure.map_map (measurable_fst.prodMk horbit) hprod.measurable] at ht
  exact ht

end InvariantIsing

end

end OAI
