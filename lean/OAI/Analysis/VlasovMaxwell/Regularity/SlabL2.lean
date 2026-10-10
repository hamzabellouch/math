import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.PicardContraction

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def SlabTimeContinuousL2 (T : ℝ) (F : Field) : Prop :=
  ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t∈Icc 0 T, (F₂ t : Vec → Vec)=ᵐ[volume] (fun x => F (t,x))

lemma slabTimeContinuousL2_compact {F : Field} {T : ℝ} (hT : 0≤T)
    (hF : ContinuousOn F (fieldSlab T)) {K : Set Vec} (hK : IsCompact K)
    (hz : ∀ t∈Icc 0 T, ∀ x∉K, F (t,x)=0) : SlabTimeContinuousL2 T F := by
  let c : ℝ → ℝ := fun t => max 0 (min T t)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcm (t : ℝ) : c t∈Icc 0 T := ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
  have hce (t : ℝ) (ht : t∈Icc 0 T) : c t=t := by
    dsimp [c]; rw [min_eq_right ht.2,max_eq_right ht.1]
  let G : Field := fun p => F (c p.1,p.2)
  have hG : Continuous G := by
    apply continuousOn_univ.mp
    exact hF.comp (((hc.comp continuous_fst).prodMk continuous_snd).continuousOn) (fun p hp => hcm p.1)
  have hL := timeContinuousL2_compact hG (fun U hU => ⟨K,hK,fun t ht x hx => hz _ (hcm t) x hx⟩)
  obtain ⟨G₂,hGc,hGe⟩ := hL
  refine ⟨G₂,hGc.mono (fun t ht => ht.1),fun t ht => ?_⟩
  simpa only [G,hce t ht] using hGe t ht.1

lemma slabTimeContinuousL2_of_exterior {F G : Field} {T : ℝ} (hT : 0≤T)
    (hF : ContinuousOn F (fieldSlab T)) (hG : Continuous G) (hGL : TimeContinuousL2 G)
    {K : Set Vec} (hK : IsCompact K) (hz : ∀ t∈Icc 0 T, ∀ x∉K, F (t,x)=G (t,x)) :
    SlabTimeContinuousL2 T F := by
  have hL := slabTimeContinuousL2_compact hT (hF.sub hG.continuousOn) hK
    (fun t ht x hx => sub_eq_zero.mpr (hz t ht x hx))
  obtain ⟨D₂,hDc,hDe⟩ := hL
  obtain ⟨G₂,hGc,hGe⟩ := hGL
  refine ⟨fun t => G₂ t+D₂ t,(hGc.mono (fun t ht => ht.1)).add hDc,?_⟩
  intro t ht
  filter_upwards [Lp.coeFn_add (G₂ t) (D₂ t),hGe t ht.1,hDe t ht] with x ha hg hd
  rw [ha]
  change (G₂ t : Vec → Vec) x+(D₂ t : Vec → Vec) x=F (t,x)
  rw [hg,hd]
  exact add_sub_cancel _ _

lemma picard_limit_slab_l2 {d : Datum} {S : ℕ → Solution} {E B : Field} {T A R P : ℝ}
    (hT : 0≤T) (hEc : ContinuousOn E (fieldSlab T)) (hBc : ContinuousOn B (fieldSlab T))
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)))
    (hV : ∀ n, TransportFor (S (n+1)) (S n).E (S n).B)
    (hb : ∀ n, LocalParticleBound T A R P (S (n+1)).f)
    (hEl : TendstoUniformlyOn (fun n => (S n).E) E atTop (fieldSlab T))
    (hBl : TendstoUniformlyOn (fun n => (S n).B) B atTop (fieldSlab T)) :
    SlabTimeContinuousL2 T E ∧ SlabTimeContinuousL2 T B := by
  have he := picard_uniform_limit_exterior hsm hr hV hb hEl hBl
  have hn (x : Vec) (hx : x∉closedBall (0:Vec) (R+T)) : R+T<‖x‖ := by
    simpa only [mem_closedBall,dist_zero_right,not_le] using hx
  exact ⟨slabTimeContinuousL2_of_exterior hT hEc (hr 0).smooth_E.continuous (hr 0).l2E
    (isCompact_closedBall (0:Vec) (R+T)) (fun t ht x hx => (he t ht x (hn x hx)).1),
    slabTimeContinuousL2_of_exterior hT hBc (hr 0).smooth_B.continuous (hr 0).l2B
    (isCompact_closedBall (0:Vec) (R+T)) (fun t ht x hx => (he t ht x (hn x hx)).2)⟩

end RVM
end

end OAI
