import OAI.Geometry.Convex.GeneralMahler.Parameter
import OAI.Geometry.Convex.GeneralMahler.Cutoff

namespace OAI
/-! Continuity for the normalization update. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler

lemma cluster_unique {F : Type*} [NormedAddCommGroup F] [ProperSpace F] (f : ℕ→F) (b : F)
    {C : ℝ} (hc : ∀ᶠ n in atTop, ‖f n‖ ≤ C)
    (hh : ∀ (u:ℕ→ℕ) (x:F), StrictMono u → Tendsto (f∘u) atTop (𝓝 x) → x=b) :
    Tendsto f atTop (𝓝 b) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra hn
  let s := closedBall (0:F) C \ ball b ε
  have h : ∃ᶠ n in atTop, f n∈s := by
    have hi : ∃ᶠ n in atTop, f n∉ball b ε := by simpa [Filter.Frequently] using hn
    apply (hi.and_eventually hc).mono (fun x h=>?_)
    exact ⟨mem_closedBall_zero_iff.mpr h.2, h.1⟩
  obtain ⟨x,hx,u,hu,he⟩ := ((isCompact_closedBall (0:F) C).diff isOpen_ball).tendsto_subseq' h
  exact hx.2 (hh u x hu he ▸ mem_ball_self hε)

variable {m:ℕ} {R:ℝ}

lemma tendsto_inv_action {p : ℕ → Rn m ≃L[ℝ] Rn m}
    (q : Rn m ≃L[ℝ] Rn m)
    {C:ℝ} (hC : ∀ n, ‖(p n).symm.toContinuousLinearMap‖ ≤ C)
    (ht : ∀ x, Tendsto (fun n => p n x) atTop (𝓝 (q x)))
    {v : ℕ → Rn m} {y:Rn m} (hv : Tendsto v atTop (𝓝 y)) :
    Tendsto (fun n => (p n).symm (v n)) atTop (𝓝 (q.symm y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he := hv.sub (ht (q.symm y))
  rw [q.apply_symm_apply,sub_self] at he
  have hh : Tendsto (fun n=> C* ‖v n-p n (q.symm y)‖) atTop (𝓝 0) := by
    simpa using he.norm.const_mul C
  apply squeeze_zero _ _ hh
  · intro n; positivity
  intro n
  have hu : (p n).symm (v n)-q.symm y=(p n).symm (v n-p n (q.symm y)) := by rw [_root_.map_sub];simp
  rw [hu]
  apply (((p n).symm.toContinuousLinearMap).le_opNorm _).trans
  gcongr; exact hC n

namespace Param

theorem cont_B : Continuous (@B m R) := continuous_fst.comp continuous_subtype_val
theorem cont_T : Continuous (@T m R) := continuous_snd.comp continuous_subtype_val

theorem cont_S : Continuous (@S m R) :=
  CFC.continuousOn_sqrt.comp_continuous (continuous_const.add cont_T)
    (fun x=> (form_posDef (by norm_num) (add_cov_box x.in_box.2)).posSemidef.nonneg)

theorem cont_trans (h:0<R) :
    Continuous fun p : Param m R × Rn m => (p.1.transE h) p.2 := by
  simp_rw [trans_apply]
  apply Continuous.clm_apply ((continuous_op.comp cont_B).comp continuous_fst) continuous_snd

variable (q : ProjField m)
theorem norm_proj (C : ProperCone ℝ (Rn m)) (x) :
    ‖coneProj C x‖ ≤ ‖x‖ := by
  simpa [proj_of_mem C C.zero_mem] using ((coneProj_lip C).dist_le_mul x 0)

theorem proj_cont (h:0<R) :
    Continuous fun p : Param m R × Rn m =>
      coneProj (p.1.instanceQ h q).C p.2 := by
  apply continuous_iff_seqContinuous.mpr
  rintro f a hf
  set B : Param m R → Rn m≃L[ℝ]Rn m := fun x => x.transE h
  set y := fun p : Param m R × Rn m => coneProj (p.1.instanceQ h q).C p.2
  have hh : ∀ᶠ n in atTop, ‖(f n).2‖ ≤ ‖a.2‖+1 :=
    hf.snd_nhds.norm (Iic_mem_nhds (by linarith))
  change Tendsto (y∘f) atTop (𝓝 (y a))
  apply cluster_unique _ _ (hc := hh.mono fun i hi=>(norm_proj _ _).trans hi)
  intro u x hu ht
  let g := f∘u
  have hl : Tendsto g atTop (𝓝 a) := hf.comp hu.tendsto_atTop
  have hlim (w): Tendsto (fun n=> B (g n).1 w) atTop (𝓝 (B a.1 w)) :=
    ((cont_trans h).tendsto _).comp (hl.fst_nhds.prodMk_nhds tendsto_const_nhds)
  have hC (x : Param m R) : ‖(B x).symm.toContinuousLinearMap‖ ≤ R :=
    (inv_norm_box _ h x.in_box.1 _ (equivPD_spec _)).2
  have hv := tendsto_inv_action (B a.1) (p := fun n=>B (g n).1)
    (fun n=>hC _) hlim ht
  have he : x ∈ (a.1.instanceQ h q).C := by
    apply (q.C.isClosed.mem_of_tendsto hv)
    apply Eventually.of_forall
    intro n
    exact (proj_mem ( (g n).1.instanceQ h q).C (g n).2)
  apply Eq.symm; apply proj_unique _ he
  intro z hz
  change (B a.1).symm z ∈ q.C at hz
  let w := (B a.1).symm z
  have hr := hlim w
  rw [show B a.1 w=z from (B a.1).apply_symm_apply z] at hr
  have hp := (hl.snd_nhds.sub ht).inner (𝕜 := ℝ) (hr.sub ht)
  refine le_of_tendsto hp (Eventually.of_forall fun n=>?_ )
  apply proj_vi (( (g n).1.instanceQ h q).C)
  change ((B _).symm ((B (g n).1) w))∈ q.C
  rwa [(B _).symm_apply_apply]

theorem mean_cont (_hr : 2≤R) (h:0<R) :
    Continuous fun p : Param m R × Rn m =>
      mean (p.1.instanceQ h q).C (p.1.instanceQ h q).root p.2 := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let F (p : Param m R × Rn m) (x : Rn m) :=
    sample (p.1.instanceQ h q).C (p.1.instanceQ h q).root p.2 x
  let g := fun x:Rn m=> (2:ℝ) * ‖x‖ + (‖p.2‖+1)
  have hg : Integrable g (normal m) :=
    ((ProjField.i_norm m).const_mul _).add (integrable_const _)
  change ContinuousAt (fun p => ∫ x, F p x ∂normal m) p
  have he : ∀ᶠ p' in 𝓝 p, ‖p'.2‖ ≤ ‖p.2‖ + 1 :=
    continuous_snd.norm.continuousAt (Iic_mem_nhds (by linarith))
  apply continuousAt_of_dominated (Eventually.of_forall fun _ =>
    (continuous_sample ..).aestronglyMeasurable)
    (he.mono fun p' hp => ae_of_all _ ?_) hg (ae_of_all _ ?_)
  · intro x
    have ha : Continuous (fun p : Param m R × Rn m => F p x) := by
      let v := fun p: Param m R × Rn m => op p.1.S x + p.2
      have hv : Continuous v :=
        (Continuous.clm_apply ((continuous_op.comp cont_S).comp continuous_fst)
          continuous_const).add continuous_snd
      convert (proj_cont q h).comp (continuous_fst.prodMk hv) using 1
      ext p : 1
      change coneProj _ ((equivPD p.1.S_pos x)+p.2) = _
      congr 2
      change (equivPD p.1.S_pos).toContinuousLinearMap x=op _ _
      rw [equivPD_spec]
    exact ha.continuousAt
  · intro x
    let p := p'.1
    have H := norm_proj (p.instanceQ h q).C (affineN (p.instanceQ h q).root p'.2 x)
    apply H.trans ((norm_add_le ..).trans ?_)
    apply add_le_add _ hp
    have hb := equivPD_spec p.S_pos
    change ‖(equivPD p.S_pos).toContinuousLinearMap x‖ ≤ _
    rw [equivPD_spec]; apply ((op p.S).le_opNorm x).trans
    gcongr
    rw [op_norm]
    exact (inv_norm_box 2 (by norm_num) (A := p.S) (by simpa using p.S_box)
      (equivPD p.S_pos) hb).1

section
variable [NeZero m]
omit [NeZero m] in
lemma U_cont (h:0<R) : Continuous fun p:Param m R => (p.instanceQ h q).U := by
  have hh : Continuous (fun p:Param m R=> (id p,q.U)) :=
    continuous_id.prodMk continuous_const
  have he := (cont_trans (m := m) h).comp hh
  exact he
theorem shift_cont (hr : 2≤R) (h:0<R) (z : ℝ) :
    Continuous fun p : Param m R => (p.instanceQ h q).shift z := by
  obtain ⟨K,hk⟩ := q.Field_isBound
  have hh : 1 ≤ K*R := by nlinarith [hk.one_le]
  obtain ⟨C,hc,he⟩ := ProjField.layers_growth m hh
  apply continuous_iff_seqContinuous.mpr
  intro f a ha
  let g := fun p : Param m R => p.instanceQ h q
  refine cluster_unique (fun i=> (g (f i)).shift z) ((g a).shift z) (hc := Eventually.of_forall
    fun i => he (g (f i)) ((f i).Bound_instance hr h hk) z) ?_
  intro u x hu hx
  have h₂ := ha.comp hu.tendsto_atTop
  apply mean_injective (g a).C (g a).root ⟨_,(g a).U_in⟩
  have H (p:Param m R) : mean (g p).C (g p).root ((g p).shift z) = Layers.a z • (g p).U :=
    (g p).XT_mean _
  rw [H]
  have h₁ := ((mean_cont q hr h).tendsto (a,x)).comp (h₂.prodMk_nhds hx)
  have HU : Continuous (fun p:Param m R => (g p).U) := U_cont q h
  have hU : Continuous (fun p : Param m R=>Layers.a z • (g p).U) := (continuous_const (y := Layers.a z)).smul HU
  have hv : Tendsto (fun i => mean (g (f (u i))).C (g (f (u i))).root ((g (f (u i))).shift z)) atTop
      (𝓝 (mean (g a).C (g a).root x)) := h₁
  simp_rw [H] at hv
  exact tendsto_nhds_unique hv ((hU.tendsto a).comp h₂)
end
end Param
end GeneralMahler

end

end OAI
