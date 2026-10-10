import OAI.Probability.ContinuumTransition.ConstructionStage

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

structure StageTransition {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n)
    (s' : ConstructionStage t p τ (n+1)) (Rnew : ℝ) : Prop where
  range_large : 4 < Rnew
  mass_eq : s'.σ = prepend s.a s.σ
  range_eq : s'.R = prepend Rnew s.R
  next_small : s'.a < geometricBudget n/2
  displacement : dist s'.x s.x < geometricBudget n/32
  approximation : ∀ y ∈ closedBall initialPoint (1/4), |s'.pressure y-s.ideal y| ≤ geometricBudget n

lemma construction_step {t p τ γ : ℝ} (hp : 0 < p) (hτ : 0 < τ) (hτp : τ ≤ p/100)
    (hγ : 0 < γ) (hcap : ConstructionCap t (firstMass p+1))
    (hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
      closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w))
    {n : ℕ} (s : ConstructionStage t p τ n) :
    ∃ s' : ConstructionStage t p τ (n+1), ∃ Rnew, StageTransition s s' Rnew := by
  have hWmod : closedBall initialPoint (1/4) ⊆ moderateBox :=
    (closedBall_subset_closedBall (by norm_num : (1:ℝ)/4 ≤ 1/2)).trans initial_ball_moderate
  have hball := s.near_moderate.trans (hWmod.trans moderateBox_subset)
  have hxmod : s.x ∈ moderateBox := hWmod (s.x_near.le.trans (by norm_num : (1:ℝ)/8 ≤ 1/4))
  have hxdom := moderateBox_subset hxmod
  have hsl := s.triple.support_ball hp (groupRadius_le hτ.le n) hτp hgeom
  have hb : groupRadius τ n ≤ p/100 := (groupRadius_le hτ.le n).trans hτp
  let ε := τ*geometricBudget n/4
  have hε : 0 < ε := by dsimp [ε]; positivity [geometricBudget_pos n]
  obtain ⟨S,hS,δ,hδ,hpersist⟩ := three_group_persistence (s.convex hcap) hxdom
    (show (0:ℝ) < 1/8 by norm_num) hγ hball hsl
    (slopeGroups_convex s.ideal s.x (triangleVertex p) (groupRadius τ n))
    (fun i j hij => HasVertexTriple.separated hp hb i j hij) s.triple.hull hε
    (fun _ => inter_subset_right) (1048576^2) 1048576
  let ell := geometricBudget n/32
  have hell : 0 < ell := by dsimp [ell]; positivity [geometricBudget_pos n]
  let a := min δ (min (ell/(S+1)) (geometricBudget n/2))/2
  have ha : 0 < a := by dsimp [a]; positivity [geometricBudget_pos n]
  have ham : a < min δ (min (ell/(S+1)) (geometricBudget n/2)) := by dsimp [a] at ha ⊢; linarith
  have haδ : a < δ := ham.trans_le (min_le_left _ _)
  have haell : a < ell/(S+1) := ham.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hapow : a < geometricBudget n/2 := ham.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hSa : S*a < ell := by
    have hh := (lt_div_iff₀ (show 0 < S+1 by linarith)).mp haell
    nlinarith only [hh,ha]
  obtain ⟨B,hB,hbound⟩ := s.referenceBounded
  have hprec : 0 < min (a^2) (geometricBudget n) := lt_min (sq_pos_of_pos ha) (geometricBudget_pos n)
  obtain ⟨Rnew,hRnew,hRbig,happ⟩ := physical_kac_approximate hcap s.a_pos s.σ_nonneg s.R_one s.σ_summable
    s.mass_total hB hbound hprec (B+1)
  let σ' := prepend s.a s.σ
  let R' := prepend Rnew s.R
  have hσ' : ∀ k, 0 ≤ σ' k := prepend_nonneg s.a_pos.le s.σ_nonneg
  have hR' : ∀ k, 1 ≤ R' k := prepend_ge_one (by linarith) s.R_one
  have hs' : Summable σ' := summable_prepend s.a s.σ_summable
  have hmass' : ∑' k, σ' k = s.a+∑' k, s.σ k := tsum_prepend s.a s.σ_summable
  have hm' : ∑' k, σ' k ≤ firstMass p+1 := hmass' ▸ s.mass_total
  have htot : a+∑' k, σ' k ≤ firstMass p+1-geometricBudget (n+1) := by
    rw [hmass',geometricBudget_succ]
    linarith only [s.mass,hapow]
  have haM : a ≤ firstMass p+1 := by
    have hh : 0 ≤ ∑' k, σ' k := tsum_nonneg hσ'
    have hh' := geometricBudget_pos (n+1)
    linarith only [htot,hh,hh']
  let Q := physicalPressure (physicalProfile t σ' R') t
  let P := meanField Q a
  have hQ := physical_convex_bounded hcap.t_large hσ' hR' hs' (hcap.weak hm')
  have hMF := physical_meanField_bounded hcap.t_large ha hσ' hR' hs' (hcap.weak hm') (hcap.lt_gap haM)
  obtain ⟨z,hz,hzr,hg,hull⟩ := hpersist a ha haδ Q P hQ hMF.1 hMF.2
    (fun y hy => (happ y (s.near_moderate hy)).trans (min_le_left _ _))
    (physical_transform_gain hcap.t_large ha hσ' hR' hs' (hcap.weak hm') (hcap.lt_gap haM)
      hxmod.1 hxmod.2.1 hxmod.2.2)
    (fun y hy w hw => by
      have hh := hWmod (s.near_moderate hy)
      have hd := physical_transform_active_bound hcap.t_large ha hσ' hR' hs' (hcap.weak hm') (hcap.lt_gap haM)
        hh.1 hh.2.1 hh.2.2 hw
      simpa only [abs_of_nonneg hd.1] using hd.2)
  have hdisp : dist z s.x < geometricBudget n/32 := hz.trans hSa
  let s' : ConstructionStage t p τ (n+1) := {
    σ := σ', R := R', a := a, x := z,
    σ_nonneg := hσ', R_one := hR', σ_summable := hs', a_pos := ha, mass := htot,
    referenceBounded := ⟨Rnew,by linarith,by
      intro k hk
      cases k with
      | zero => exact le_refl _
      | succ k => exact (hbound k hk).trans (by linarith)⟩,
    location := by
      rw [locationRadius_succ]
      have hh := dist_triangle z s.x initialPoint
      linarith only [hh,hdisp,s.location],
    triple := ⟨hg,by rw [groupRadius_succ]; exact hull⟩ }
  refine ⟨s',Rnew,hRnew,rfl,rfl,hapow,hdisp,?_⟩
  intro y hy
  exact (happ y hy).trans (min_le_right _ _)

end ContinuumTemperature
end
end

end OAI
