import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ChartHopfLocalization
import OAI.Analysis.BiholderTransport.Regularity.KernelBounds
import OAI.Analysis.BiholderTransport.Convexity.StrongEnvelope
import OAI.Analysis.BiholderTransport.Convexity.FamilySemiconvex

namespace OAI

noncomputable section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma uniform_family_short_envelope_data {Φ : P×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {Kp : Set P} (hKp : IsCompact Kp) (hmono : ∀ p∈Kp,Monotone (fun s=>Φ (p,s)))
    {Lφ : ℝ≥0} (hφL : ∀ p∈Kp,LipschitzWith Lφ (fun s=>Φ (p,s)))
    (A B : ℝ) (a : M) :
    ∃ J JY : ℝ≥0,∃ r>0,∃ δ>0,∀ p∈Kp,∀ u : M → ℝ,Continuous u →
      (∀ y,cTransform u y∈Icc A B) → ∀ t : ℝ,0<t → t<δ →
      let F := fun z : Model n => t*hopfLax t (fun y => Φ (p,cTransform u y))
        ((extChartAt 𝓘(ℝ,Model n) a).symm z)
      (∀ z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,DifferentiableAt ℝ F z) ∧
      LipschitzOnWith J (fderiv ℝ F) (ball (extChartAt 𝓘(ℝ,Model n) a a) (r/4)) ∧
      ∃ Y0 : Model n → M,
        LipschitzOnWith JY (fun z => extChartAt 𝓘(ℝ,Model n) a (Y0 z))
          (ball (extChartAt 𝓘(ℝ,Model n) a a) r) ∧
        ∀ z∈ball (extChartAt 𝓘(ℝ,Model n) a a) r,
          Y0 z∈(extChartAt 𝓘(ℝ,Model n) a).source ∧
          ∀ y:M,hopfLax t (fun y => Φ (p,cTransform u y))
            ((extChartAt 𝓘(ℝ,Model n) a).symm z)=
            Φ (p,cTransform u y)+cost y ((extChartAt 𝓘(ℝ,Model n) a).symm z)/t ↔ y=Y0 z := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let C : Model n → Model n → ℝ := fun y z => chartCost a (χ.symm z) y
  have hc : ContDiffAt ℝ ∞ (Function.uncurry C) (χ a,χ a) :=
    (chartCost_pair_contDiffAt_diagonal (mem_extChartAt_target (I := 𝓘(ℝ,Model n)) a)).comp
      (χ a,χ a) (contDiffAt_snd.prodMk contDiffAt_fst)
  obtain ⟨K,H,hK,hH,Rk,hRk,hCs,hrem,hcross⟩ := smooth_kernel_local_bounds hc
  obtain ⟨m,hm,R0,hR0,V0,hV0,δ0,hδ0,hR0T,hs⟩ :=
    uniform_family_short_action_strongConvex (n := n) hΦ hKp hmono A B a
  let R := min R0 (Rk/2)
  have hR : 0<R := lt_min hR0 (half_pos hRk)
  have hS0 : closedBall (χ a) R⊆closedBall (χ a) R0 :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hSk : closedBall (χ a) R⊆ball (χ a) Rk :=
    closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hRk))
  let D : ℝ≥0 := ⟨Metric.diam (univ : Set M),Metric.diam_nonneg⟩
  obtain ⟨δ1,hδ1,V1,hV1,hlocal⟩ := uniform_hopfLax_chart_localization (n := n) (Lφ*D) a hR
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hV0 (inter_mem hV1 (ball_mem_nhds (χ a) hRk)))
  refine ⟨Real.toNNReal (6*(H+K^2/m)),Real.toNNReal (2*K/m),r,hr,min δ0 δ1,lt_min hδ0 hδ1,?_⟩
  intro p hp u hu hb t ht htδ
  let w : M → ℝ := fun y => Φ (p,cTransform u y)
  have hw : LipschitzWith (Lφ*D) w := (hφL p hp).comp
    (cTransform_lipschitz hu (fun x y =>
      Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)))
  let F : Model n → ℝ := fun z => t*hopfLax t w (χ.symm z)
  let W : Model n → ℝ := fun y => t*w (χ.symm y)
  choose Y0 hY0 hmin0 using (fun z : Model n => exists_hopfLax_minimizer hw.continuous t (χ.symm z))
  let Y : Model n → Model n := fun z => χ (Y0 z)
  have hycoord (z:Model n) (hz:z∈ball (χ a) r) :
      Y0 z∈χ.source ∧ Y z∈ball (χ a) R :=
    hlocal t ht (lt_of_lt_of_le htδ (min_le_right _ _)) z (hrV hz).2.1 w hw (Y0 z) (hY0 z)
  have hY : ∀ z∈ball (χ a) r,Y z∈closedBall (χ a) R :=
    fun z hz => ball_subset_closedBall ((hycoord z hz).2)
  have hval : ∀ z∈ball (χ a) r,F z=W (Y z)+C (Y z) z := by
    intro z hz
    dsimp only [F,W,C,chartCost,Y]
    rw [χ.left_inv (hycoord z hz).1,hY0 z]
    field_simp
  have hmin : ∀ z∈ball (χ a) r,∀ y∈closedBall (χ a) R,F z≤W y+C y z := by
    intro z hz y hy
    have HH := mul_le_mul_of_nonneg_left (hopfLax_le hw.continuous t (χ.symm z) (χ.symm y)) ht.le
    dsimp only [F,W,C,chartCost]
    simpa only [mul_add,←mul_div_assoc,mul_div_cancel_left₀ _ ht.ne'] using HH
  have hstrong : ∀ z∈ball (χ a) r,
      StrongConvexOn (closedBall (χ a) R) m (fun y => W y+C y z) := by
    intro z hz
    have HH := hs p hp u hu hb t ht (lt_of_lt_of_le htδ (min_le_left _ _)) z (hrV hz).1
    exact ⟨convex_closedBall _ _,fun {x} hx {y} hy {p} {q} hp hq hsum =>
      HH.2 (hS0 hx) (hS0 hy) hp hq hsum⟩
  have HC : ∀ y∈closedBall (χ a) R,∀ y'∈closedBall (χ a) R,
      ∀ z∈ball (χ a) r,∀ z'∈ball (χ a) r,
      |C y' z'-C y' z-C y z'+C y z|≤K*‖y'-y‖*‖z'-z‖ :=
    fun y hy y' hy' z hz z' hz' => hcross y (hSk hy) y' (hSk hy')
      z (hrV hz).2.2 z' (hrV hz').2.2
  have HR : ∀ z∈ball (χ a) r,∀ z'∈ball (χ a) r,
      |C (Y z) z'-C (Y z) z-fderiv ℝ (C (Y z)) z (z'-z)|≤H*‖z'-z‖^2 :=
    fun z hz z' hz' => hrem (Y z) (hSk (hY z hz)) z (hrV hz).2.2 z' (hrV hz').2.2
  obtain ⟨hd,hLip⟩ := strong_envelope_C11 hr hm hK hH hY hval hmin hstrong HC HR
  refine ⟨fun z hz => (hd z hz).differentiableAt,hLip,Y0,
    strong_envelope_minimizer_lipschitz hm hK hY hval hmin hstrong HC,?_⟩
  intro z hz
  refine ⟨(hycoord z hz).1,?_⟩
  intro y
  constructor
  · intro hy
    have hym := hlocal t ht (lt_of_lt_of_le htδ (min_le_right _ _))
      z (hrV hz).2.1 w hw y hy
    have hyeq : F z=W (χ y)+C (χ y) z := by
      dsimp only [F,W,C,chartCost]
      rw [χ.left_inv hym.1,hy]
      field_simp
      rfl
    have he := strongly_convex_minimizer_unique hm (hstrong z hz) (hY z hz)
      (ball_subset_closedBall hym.2)
      (show IsMinOn (fun y => W y+C y z) (closedBall (χ a) R) (Y z) from by
        intro y' hy'
        change W (Y z)+C (Y z) z≤W y'+C y' z
        rw [←hval z hz]
        exact hmin z hz y' hy') ((hval z hz).symm.trans hyeq)
    exact χ.injOn hym.1 (hycoord z hz).1 he.symm
  · rintro rfl
    exact hY0 z

end WeakMTWTransport

end

end OAI
