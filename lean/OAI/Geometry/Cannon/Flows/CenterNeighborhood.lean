import Mathlib
import OAI.Geometry.Cannon.Flows.OscillationMonoRange
import OAI.Geometry.Cannon.Flows.FlowPuncture
import OAI.Geometry.Cannon.Flows.FlowPaid

namespace OAI

section
section
section
noncomputable section
section
section
namespace CannonApprox

open Set Metric Filter Topology CannonNode CannonMagnification CannonPairs

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

omit [CompactSpace X] in
lemma FlowSetup.center_neighborhood {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hB : 0 ≤ F.B+1) (g : ℕ) (i : Fin (F.S.flow.size g)) :
    closedBall (F.S.center g i) F.ε ⊆ T.Ω := by
  intro y hy
  apply F.local_domain
  have hx := mem_closedBall.mp (F.S.center_mem hB g i)
  rw [mem_closedBall] at hy ⊢
  linarith only [dist_triangle y (F.S.center g i) T.x₀,hy,hx]

theorem FlowPatternSetup.paid_alternative (T : RecordData action ι p r)
    {ell L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T ell L CE LE Q)
    (gi : ∀ g, Fin (F.S.flow.size g) → Γ)
    (P : FlowPatternSetup T F (fun g i => action (gi g i)))
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (hB : 0 ≤ F.B) (U V A cutoff : ℝ) (hV : 0 < V) (hA : 0 < A)
    (hwide : 3*U/T.H_diameter < A) (hroom : 2*U/A ≤ F.ε)
    (g : ℕ) (i j : Fin (F.S.flow.size g))
    (hi : F.S.good (F.S.state g i)) (hj : F.S.good (F.S.state g j))
    (hpat : P.pat g i=P.pat g j)
    (hui : ∀ y, dist (action (gi g i) y) (action (gi g i) T.z₀)*
      denominator (F.S.center g i) (F.S.scale g) y ≤ U*F.S.scale g)
    (huj : ∀ y, dist (action (gi g j) y) (action (gi g j) T.z₀)*
      denominator (F.S.center g j) (F.S.scale g) y ≤ U*F.S.scale g)
    (hli : ∀ y, denominator (F.S.center g i) (F.S.scale g) y ≤ cutoff →
      F.S.scale g ≤ V*dist (action (gi g i) y) (action (gi g i) T.z₀)*
        denominator (F.S.center g i) (F.S.scale g) y)
    (hlj : ∀ y, denominator (F.S.center g j) (F.S.scale g) y ≤ cutoff →
      F.S.scale g ≤ V*dist (action (gi g j) y) (action (gi g j) T.z₀)*
        denominator (F.S.center g j) (F.S.scale g) y)
    (hsmall : (F.B+2)*F.S.scale g ≤ cutoff)
    (havoid : A*F.S.scale g < 1/(V*(F.B+2)))
    (hfar : 2*A*F.S.scale g ≤ dist (action (gi g i) T.z₀) (action (gi g j) T.z₀)) :
    (min (F.S.κ/4) (1/16))*F.S.len g i ≤ CannonCrossEnergy.oscillation T.f
      ((action (gi g i)).symm '' closedBall (action (gi g j) T.z₀) (A*F.S.scale g)) ∨
    (min (F.S.κ/4) (1/16))*F.S.len g j ≤ CannonCrossEnergy.oscillation T.f
      ((action (gi g j)).symm '' closedBall (action (gi g i) T.z₀) (A*F.S.scale g)) := by
  obtain ⟨v₀,v₁,γ,hγ,hgap,hball,hsep⟩ := P.data g i hi
  obtain ⟨w₀,w₁,γ',hγ',hgap',hball',hsep'⟩ := P.data g j hj
  apply T.pattern_pair hr hrlim hpnet (gi g i) (gi g j) (F.S.center g i) (F.S.center g j)
    (action (gi g i) T.z₀) (action (gi g j) T.z₀) (F.S.scale g) U V A (F.B+2) cutoff F.ε
    (radius_pos _ _) hV hA (by linarith only [hB]) hwide hroom
    (F.center_neighborhood (by linarith only [hB]) g i)
    (F.center_neighborhood (by linarith only [hB]) g j)
    hui huj hli hlj hsmall havoid hfar
    (fun s => closedBall (P.pat g i s : X) (3*F.cPat*radius ell (160*(Q+1)*F.n)))
    hball (by intro s; simpa only [hpat] using hball' s)
    v₀ v₁ γ hγ F.S.κ (F.S.len g i) (F.S.len g j) F.S.κpos
    (F.S.len_pos g i) (F.S.len_pos g j) hgap
  simpa only [hpat] using hsep'

end CannonApprox

end

section

namespace CannonPairs

open Set Metric CannonMagnification CannonCrossEnergy MeasureTheory

theorem exists_cost_measure_threshold {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (Ω : Set X) (f : X → ℝ) (ν : FiniteMeasure X) (E B ε C L U V cutoff A S : ℝ)
    (x₀ : X) (hε : 0 < ε) (hB : 0 < B) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hU : 0 < U) (hV : 0 < V)
    (hcut : 0 < cutoff) (hA : 0 < A) (hS : 0 < S) (hcoef : 2*L*A*U^2 ≤ S)
    (hf : ContinuousOn f Ω) (hloc : closedBall x₀ (2*ε) ⊆ Ω)
    (hmeasure : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ x ∈ K,
        closedBall x s ⊆ Ω ∧ (oscillation f (closedBall x s))^2 ≤ E*(ν (closedBall x (B*s)) : ℝ)) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ (h : X ≃ₜ X) (x p p' : X) (R t lam : ℝ),
      x ∈ closedBall x₀ ε → 0 < R → 0 < t → t ≤ t₀ →
      Expansion h x R C L →
      (∀ y, dist (h y) p*denominator x R y ≤ U*R) →
      (∀ y, denominator x R y ≤ cutoff → R ≤ V*dist (h y) p*denominator x R y) →
      R=dist p' p*t → 2*A*R ≤ dist p' p → 0 ≤ lam →
      lam ≤ oscillation f (h.symm '' closedBall p' (A*R)) →
      lam^2/(E+1) ≤ (ν (closedBall (h.symm p') (B*(S*t^2))) : ℝ) ∧
      h '' closedBall (h.symm p') (B*(S*t^2)) ⊆ closedBall p' ((2*C*V^2*B*S)*R) ∧
      closedBall (h.symm p') (B*(S*t^2)) ⊆ closedBall x ((U+B*S)*t) := by
  have hKΩ : closedBall x₀ (3*ε/2) ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith only [hε])).trans hloc
  obtain ⟨s₀,hs₀,hbound⟩ := hmeasure _ isClosed_closedBall.isCompact hKΩ
  let t₀ := min 1 (min (s₀/S) (min (ε/(2*U)) (min (cutoff/U) (1/(2*V*B*S)))))
  have ht₀ : 0 < t₀ := lt_min zero_lt_one (lt_min (div_pos hs₀ hS)
    (lt_min (div_pos hε (by positivity)) (lt_min (div_pos hcut hU) (by positivity))))
  refine ⟨t₀,ht₀,?_⟩
  intro h x p p' R t lam hx hR ht htt hexp hu hl hscale hfar hlam hosc
  have ht1 : t ≤ 1 := htt.trans (min_le_left _ _)
  have hts : t ≤ s₀/S := htt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hte : t ≤ ε/(2*U) := htt.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have htc : t ≤ cutoff/U := htt.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have htb : t ≤ 1/(2*V*B*S) := htt.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hlocal : U*t ≤ cutoff := by simpa only [mul_comm] using (le_div_iff₀ hU).mp htc
  have hsmall : 2*V*B*S*t ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 2*V*B*S)).mp htb
  have hgeom := cost_ball_geometry h x p p' R C L U V cutoff A B S t hR hC hL hU hV hA hB hS
    ht ht1 hexp hu hl hscale hfar hlocal hcoef hsmall
  have hd : 0 < dist p' p := by
    by_contra hn
    have heq := le_antisymm (le_of_not_gt hn) dist_nonneg
    rw [heq,zero_mul] at hscale
    exact (ne_of_gt hR) hscale
  have hzx : dist (h.symm p') x ≤ U*t := by
    have hh := hu (h.symm p')
    rw [h.apply_symm_apply] at hh
    nth_rewrite 2 [hscale] at hh
    have hh' : denominator x R (h.symm p') ≤ U*t :=
      (mul_le_mul_iff_right₀ hd).mp (by nlinarith only [hh])
    rw [dist_comm]
    exact (le_max_right _ _).trans hh'
  have hUt : U*t ≤ ε/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*U)).mp hte
    linarith only [hh]
  have hzK : h.symm p' ∈ closedBall x₀ (3*ε/2) := by
    rw [mem_closedBall] at hx ⊢
    linarith only [dist_triangle (h.symm p') x x₀,hzx,hUt,hx]
  have hs : 0 < S*t^2 := mul_pos hS (sq_pos_of_pos ht)
  have hss : S*t^2 ≤ s₀ := by
    have hh := (le_div_iff₀ hS).mp hts
    have hsq : t^2 ≤ t := by nlinarith only [ht,ht1]
    nlinarith only [hh,mul_le_mul_of_nonneg_left hsq hS.le]
  obtain ⟨hball,hmeas⟩ := hbound _ hs hss _ hzK
  have hb := (isCompact_closedBall (h.symm p') (S*t^2)).image_of_continuousOn (hf.mono hball)
  have hsub : f '' (h.symm '' closedBall p' (A*R)) ⊆ f '' closedBall (h.symm p') (S*t^2) :=
    image_mono hgeom.1
  have hne : (h.symm '' closedBall p' (A*R)).Nonempty :=
    (nonempty_closedBall.mpr (mul_pos hA hR).le).image h.symm
  have hosc' := hosc.trans (oscillation_mono_range hne hb.bddAbove hb.bddBelow hsub).2
  have hsq := (pow_le_pow_left₀ hlam hosc' 2).trans hmeas
  refine ⟨(div_le_iff₀ (by linarith only [hE] : 0 < E+1)).mpr ?_,hgeom.2⟩
  have hn : 0 ≤ (ν (closedBall (h.symm p') (B*(S*t^2))) : ℝ) := NNReal.coe_nonneg _
  nlinarith only [hsq,hn]

end CannonPairs

end

namespace CannonApprox

open Set Metric Filter Topology MeasureTheory CannonNode CannonMagnification CannonPairs

variable {X Γ : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {action : Γ → X ≃ₜ X} {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {p : ∀ n, ι n → X} {r : ℕ → ℝ}

theorem FlowPatternSetup.cost_data {T : RecordData action ι p r} {ell L CE LE : ℝ} {Q : ℕ}
    (F : FlowSetup T ell L CE LE Q) (hell : 0 ≤ ell) (hL : 1 ≤ L)
    (hCE : 0 < CE) (hLE : 0 < LE) (hdiam : ∀ x y : X, dist x y ≤ 1)
    (gi : ∀ g, Fin (F.S.flow.size g) → Γ)
    (P : FlowPatternSetup T F (fun g i => action (gi g i)))
    (hexp : ∀ g i, Expansion (action (gi g i)) (F.S.center g i) (F.S.scale g) CE LE)
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n) :
    ∃ c Cs Ci τ : ℝ, 0 < c ∧ 0 < Cs ∧ 0 < Ci ∧ 0 < τ ∧ F.H ≤ Cs ∧ Cs*τ ≤ 1 ∧
      ∀ g i j, F.S.good (F.S.state g i) → F.S.good (F.S.state g j) → P.pat g i=P.pat g j →
      ∀ d : ℝ, 0 < d → d ≤ 1 → F.S.scale g/d ≤ τ →
      d < dist (action (gi g i) T.z₀) (action (gi g j) T.z₀) →
        FlowPaid F gi c Cs Ci d g i j ∨ FlowPaid F gi c Cs Ci d g j i := by
  obtain ⟨_,hB,_,_,_,_,hH⟩ := F.margins hL hCE.le hLE.le
  have hB0 : 0 ≤ F.B := by linarith only [hB]
  have hB1 : 0 ≤ F.B+1 := by linarith only [hB]
  have hB2 : 0 < F.B+2 := by linarith only [hB]
  let U := CE/F.ε
  let V := 2*LE/F.ε
  have hU : 0 < U := div_pos hCE F.εpos
  have hV : 0 < V := div_pos (by positivity) F.εpos
  let A := 1+3*U/T.H_diameter+2*U/F.ε
  have hAA : 0 ≤ 3*U/T.H_diameter := (div_pos (by positivity) T.H_diameter_pos).le
  have hAB : 0 ≤ 2*U/F.ε := (div_pos (by positivity) F.εpos).le
  have hA : 0 < A := by dsimp only [A]; linarith only [hAA,hAB]
  have hwide : 3*U/T.H_diameter < A := by dsimp only [A]; linarith only [hAB]
  have hroom : 2*U/A ≤ F.ε := by
    apply (div_le_iff₀ hA).mpr
    have hh : 2*U/F.ε ≤ A := by dsimp only [A]; linarith only [hAA]
    have hh' := (div_le_iff₀ F.εpos).mp hh
    linarith only [hh']
  let Scoef := 1+2*LE*A*U^2
  have hS : 0 < Scoef := by dsimp only [Scoef]; positivity
  have hcoef : 2*LE*A*U^2 ≤ Scoef := le_add_of_nonneg_left zero_le_one
  obtain ⟨t₀,ht₀,hcost⟩ := exists_cost_measure_threshold T.Ω T.f T.ν T.E T.Cμ F.ε
    CE LE U V (F.ε/2) A Scoef T.x₀ F.εpos T.Cμ_pos T.E_nonneg hCE.le hLE.le hU hV
    (by have := F.εpos; positivity) hA hS hcoef T.continuous F.local_domain T.measure_bound
  let Cs := max F.H (U+T.Cμ*Scoef)
  let Ci := 2*CE*V^2*T.Cμ*Scoef
  have hCμ := T.Cμ_pos
  have hCs : 0 < Cs := (by positivity : 0 < U+T.Cμ*Scoef).trans_le (le_max_right _ _)
  have hCi : 0 < Ci := by dsimp only [Ci]; positivity
  let τ := min t₀ (min (F.ε/(2*(F.B+2)))
    (min (1/(2*A*V*(F.B+2))) (min (1/(2*A)) (1/Cs))))
  have hτ : 0 < τ := lt_min ht₀ (lt_min (div_pos F.εpos (by positivity))
    (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have τ₀ : τ ≤ t₀ := min_le_left _ _
  have τ₁ : τ ≤ F.ε/(2*(F.B+2)) := (min_le_right _ _).trans (min_le_left _ _)
  have τ₂ : τ ≤ 1/(2*A*V*(F.B+2)) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have τ₃ : τ ≤ 1/(2*A) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have τ₄ : τ ≤ 1/Cs := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let cp := min (F.S.κ/4) (1/16)
  have hcp : 0 < cp := lt_min (div_pos F.S.κpos (by norm_num)) (by norm_num)
  let c := cp^2/(T.E+1)
  have hEn : 0 < T.E+1 := by linarith only [T.E_nonneg]
  refine ⟨c,Cs,Ci,τ,div_pos (sq_pos_of_pos hcp) hEn,hCs,hCi,hτ,le_max_left _ _,?_,?_⟩
  · have hh := (le_div_iff₀ hCs).mp τ₄
    exact (mul_comm Cs τ).le.trans hh
  intro g i j hi hj hpat d hd hd1 hsmall hfar
  have hR : 0 < F.S.scale g := radius_pos _ _
  have hR1 : F.S.scale g ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hell) (Nat.cast_nonneg _))
  have hRratio : F.S.scale g ≤ F.S.scale g/d :=
    (le_div_iff₀ hd).mpr ((mul_le_mul_of_nonneg_left hd1 hR.le).trans_eq (mul_one _))
  have hRτ := hRratio.trans hsmall
  have hbounds (v : Fin (F.S.flow.size g)) := puncture_bounds (action (gi g v))
    (F.S.center g v) T.z₀ (F.S.scale g) CE LE F.ε hR hCE.le hLE F.εpos hR1
    (F.center_puncture hB1 g v) hdiam (hexp g v)
  have hsmall' : (F.B+2)*F.S.scale g ≤ F.ε/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(F.B+2))).mp (hRτ.trans τ₁)
    linarith only [hh]
  have havoid : A*F.S.scale g < 1/(V*(F.B+2)) := by
    apply (lt_div_iff₀ (mul_pos hV hB2)).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 2*A*V*(F.B+2))).mp (hRτ.trans τ₂)
    nlinarith only [hh]
  have hfar' : 2*A*F.S.scale g ≤ d := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*A)).mp (hsmall.trans τ₃)
    have hh' := mul_le_mul_of_nonneg_right hh hd.le
    field_simp at hh'
    nlinarith only [hh']
  have hpaid := P.paid_alternative T F gi hr hrlim hpnet hB0 U V A (F.ε/2) hV hA
    hwide hroom g i j hi hj hpat (hbounds i).1 (hbounds j).1 (hbounds i).2
    (hbounds j).2 hsmall' havoid (hfar'.trans hfar.le)
  have hcharge (i j : Fin (F.S.flow.size g))
      (hfj : d < dist (action (gi g i) T.z₀) (action (gi g j) T.z₀))
      (hpay : cp*F.S.len g i ≤ CannonCrossEnergy.oscillation T.f
        ((action (gi g i)).symm '' closedBall (action (gi g j) T.z₀) (A*F.S.scale g))) :
      FlowPaid F gi c Cs Ci d g i j := by
    let δij := dist (action (gi g j) T.z₀) (action (gi g i) T.z₀)
    have hdi : d ≤ δij := by simpa only [δij,dist_comm] using hfj.le
    have hδ : 0 < δij := hd.trans_le hdi
    let t := F.S.scale g/δij
    have ht : 0 < t := div_pos hR hδ
    have htt : t ≤ F.S.scale g/d := div_le_div_of_nonneg_left hR.le hd hdi
    have hscale : F.S.scale g=δij*t := by dsimp only [t]; field_simp
    have hlam : 0 ≤ cp*F.S.len g i := (mul_pos hcp (F.S.len_pos g i)).le
    obtain ⟨hm,him,hsrc⟩ := hcost (action (gi g i)) (F.S.center g i)
      (action (gi g i) T.z₀) (action (gi g j) T.z₀) (F.S.scale g) t (cp*F.S.len g i)
      (F.S.center_mem hB1 g i) hR ht (htt.trans (hsmall.trans τ₀))
      (hexp g i) (hbounds i).1 (hbounds i).2 hscale (hfar'.trans hdi) hlam hpay
    refine ⟨closedBall ((action (gi g i)).symm (action (gi g j) T.z₀)) (T.Cμ*(Scoef*t^2)),
      measurableSet_closedBall,?_,?_,him⟩
    · convert hm using 1
      dsimp only [c]
      ring
    · apply hsrc.trans (closedBall_subset_closedBall ?_)
      calc (U+T.Cμ*Scoef)*t ≤ Cs*t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le
           _ ≤ Cs*(F.S.scale g/d) := mul_le_mul_of_nonneg_left htt hCs.le
           _ = Cs*F.S.scale g/d := by ring
  rcases hpaid with hp | hp
  · exact Or.inl (hcharge i j hfar hp)
  · exact Or.inr (hcharge j i (by simpa only [dist_comm] using hfar) hp)

end CannonApprox

end

namespace CannonRelease
open CannonGraph CannonVisual CannonMagnification CannonPacking CannonApprox
open CannonNode CannonAnnular Set Metric Filter Topology Finset MeasureTheory

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)
local instance centerNeighborhoodSetoid : Setoid (BasedRay D) := raySetoid D

theorem boundary_no_record_flow :
    let _ := visualMetricSpace D hδ
    let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
    let ell := 2*visualExponent δ
    let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D) (r : ℕ → ℝ),
    (∀ n, 0 < r n) → Tendsto r atTop (𝓝 0) →
    (∀ n x, ∃ i, dist (p n i) x ≤ r n) →
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      (Q : ℕ), 0 < Q → ∀ CP : ℝ, 0 ≤ CP → PolynomialPacking (X:=Boundary D) Q CP →
    ∀ L : ℝ, 1 ≤ L →
      (∀ x u w : Boundary D, ∀ s : ℝ, 0 < s → dist u x ≤ s → dist w x ≤ s →
        JoinedIn (ball x (L*s)) u w) →
    FlowSetup T ell L CE LE Q → False := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
  let _ : BorelSpace (Boundary D) := ⟨rfl⟩
  dsimp only
  intro ι hι p r hr hrlim hpnet T Q hQ CP hCP hpack L hL hpaths F
  let ell := 2*visualExponent δ
  let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  have hell : 0 < ell := mul_pos (by norm_num) (visualExponent_pos δ)
  have hCE : 0 < CE := by dsimp [CE]; positivity
  have hLE : 0 < LE := by dsimp [LE]; positivity
  let gi (g : ℕ) (i : Fin (F.S.flow.size g)) :=
    ((boundaryBasedRay D (F.S.center g i)).val (F.S.kmin+160*(Q+1)*F.n*g))⁻¹
  have hexp (g : ℕ) (i : Fin (F.S.flow.size g)) :
      Expansion (boundaryHomeomorph D ⟨δ,hδ⟩ (gi g i)) (F.S.center g i) (F.S.scale g) CE LE := by
    simpa only [CannonNode.radius_eq_power, boundaryExpansion, gi, CE, LE] using
      boundaryExpansion_formula D hδ (F.S.center g i) (F.S.kmin+160*(Q+1)*F.n*g)
  have hdiam (x y : Boundary D) : dist x y ≤ 1 := boundaryDist_le_one D hδ x y
  obtain ⟨P⟩ := exists_flow_patterns T F hL hCE.le hLE.le hpaths
    (fun g i => boundaryHomeomorph D ⟨δ,hδ⟩ (gi g i)) hexp
  obtain ⟨c,Cs,Ci,τ,hc,hCs,hCi,hτ,hHCs,hCsτ,hcost⟩ :=
    P.cost_data F hell.le hL hCE hLE hdiam gi hexp hr hrlim hpnet
  obtain ⟨_,hB,_,_,_,_,hH⟩ := F.margins hL hCE.le hLE.le
  have hB1 : 0 ≤ F.B+1 := by linarith only [hB]
  obtain ⟨M,hM⟩ := flow_puncture_multiplicity D hδ T F hB1 hH Ci hCi.le
  obtain ⟨N,hN⟩ := flow_near_probability D hδ T F hB1 hH
  apply F.no_pair_data hell hQ hB1 hH CP hCP hpack hdiam gi P c Cs Ci τ hc hCs hτ
    hHCs hCsτ N M hM ?_ hcost
  intro g b
  let m := g/(160*Q*(Q+1))
  have hsum : g-m+m=g := Nat.sub_add_cancel (Nat.div_le_self _ _)
  have hh := hN (g-m) m b
  rw [hsum] at hh
  have hscale (k : ℕ) : visualScale δ k=radius ell k := by
    dsimp only [visualScale,radius,ell]
    congr 1
    push_cast
    ring
  simpa only [hscale, flowPuncture, boundaryExpansion, gi, ell, m, id_eq] using hh

end CannonRelease

end
end
end
end

end OAI
