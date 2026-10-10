import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Periodic
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Routing
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryFields

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Filter Set
open scoped Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma timeGerm_fullTimeD {v w : Field F} {t : ℝ} (h : v =ᶠ[𝓝 t] w) :
    fullTimeD v =ᶠ[𝓝 t] fullTimeD w := by
  filter_upwards [h.eventually_nhds] with s hs
  funext x
  have he : (fun r => v r x) =ᶠ[𝓝 s] (fun r => w r x) := hs.mono (fun _ he => congrFun he x)
  exact he.deriv_eq

lemma timeGerm_spaceD {v w : Field F} {t : ℝ} (h : v =ᶠ[𝓝 t] w) (i : Fin 3) :
    spaceD i v =ᶠ[𝓝 t] spaceD i w := by
  filter_upwards [h] with s hs
  funext x
  change fderiv ℝ (v s) x _ = fderiv ℝ (w s) x _
  rw [hs]

lemma timeGerm_fullMixedD {v w : Velocity} {t : ℝ} (h : v =ᶠ[𝓝 t] w) (a : MultiIndex) :
    fullMixedD a v =ᶠ[𝓝 t] fullMixedD a w := by
  induction a with
  | nil => exact h
  | cons i a ih => cases i with
    | none => exact timeGerm_fullTimeD ih
    | some i => exact timeGerm_spaceD ih i

lemma timeGerm_fullInertial {v w : Velocity} {t : ℝ} (h : v =ᶠ[𝓝 t] w) :
    fullInertial v =ᶠ[𝓝 t] fullInertial w := by
  have hd : ∀ᶠ s in 𝓝 t, ∀ i : Fin 3, spaceD i v s = spaceD i w s :=
    (Filter.eventually_all).mpr (fun i => timeGerm_spaceD h i)
  filter_upwards [h, timeGerm_fullTimeD h, hd] with s hs ht hd
  funext x
  change fullTimeD v s x + BalancedTransport.convection v s x = fullTimeD w s x + BalancedTransport.convection w s x
  simp only [BalancedTransport.convection, hs, ht, hd]

lemma timeGerm_viscous {v w : Velocity} {t : ℝ} (h : v =ᶠ[𝓝 t] w) :
    viscousCoefficient v =ᶠ[𝓝 t] viscousCoefficient w := by
  have hd : ∀ᶠ s in 𝓝 t, ∀ i : Fin 3, spaceD i (spaceD i v) s = spaceD i (spaceD i w) s :=
    (Filter.eventually_all).mpr (fun i => timeGerm_spaceD (timeGerm_spaceD h i) i)
  filter_upwards [hd] with s hd
  funext x
  change -(∑ i, spaceD i (spaceD i v) s x) = -(∑ i, spaceD i (spaceD i w) s x)
  simp only [hd]

lemma fullTimeD_translate (v : Field F) (b : ℝ) :
    fullTimeD (fun t => v (t-b)) = fun t => fullTimeD v (t-b) := by
  funext t x
  exact deriv_comp_sub_const (fun s => v s x) b t

lemma fullMixedD_translate (v : Velocity) (a : MultiIndex) (b : ℝ) :
    fullMixedD a (fun t => v (t-b)) = fun t => fullMixedD a v (t-b) := by
  induction a with
  | nil => rfl
  | cons i a ih => cases i with
    | none => simp only [fullMixedD, ih, fullTimeD_translate]
    | some i => simp only [fullMixedD, ih]; rfl

lemma fullInertial_translate (v : Velocity) (b : ℝ) :
    fullInertial (fun t => v (t-b)) = fun t => fullInertial v (t-b) := by
  ext t x i
  simp only [fullInertial, fullTimeD_translate, convection, spaceD]

lemma viscous_translate (v : Velocity) (b : ℝ) :
    viscousCoefficient (fun t => v (t-b)) = fun t => viscousCoefficient v (t-b) := rfl

lemma loadedRepeat_before_open {load v : Velocity} (hc : TimeCollars v)
    {t : ℝ} (ht : t < 5/4) : loadedRepeat load v t = load t := by
  by_cases hh : t ≤ 3/4
  · have he : afterLoadingGate t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    ext x i
    simp [loadedRepeat, he]
  · have he : repeatTemplate v t = 0 := by
      ext x i
      rw [repeatTemplate_eq hc (n := 0) (by simp only [Int.cast_zero, sub_zero]; constructor <;> linarith),
        Int.cast_zero, sub_zero, hc t (Or.inr (lt_of_not_ge hh))]
    ext x i
    simp [loadedRepeat, he]

lemma loadedRepeat_after_open {load v : Velocity} (hl : TimeCollars load) (hc : TimeCollars v)
    {t : ℝ} (ht : 3/4 < t) : loadedRepeat load v t = repeatTemplate v t := by
  by_cases hh : 1 ≤ t
  · exact loadedRepeat_after hl hh
  · have he : repeatTemplate v t = 0 := by
      ext x i
      rw [repeatTemplate_eq hc (n := 0) (by simp only [Int.cast_zero, sub_zero]; constructor <;> linarith),
        Int.cast_zero, sub_zero, hc t (Or.inr ht)]
    ext x i
    simp [loadedRepeat, he, hl t (Or.inr ht)]

lemma loadedRepeat_germ_before {load v : Velocity} (hc : TimeCollars v)
    {t : ℝ} (ht : t < 1) : loadedRepeat load v =ᶠ[𝓝 t] load := by
  filter_upwards [eventually_lt_nhds (show t < 5/4 by linarith)] with s hs
  exact loadedRepeat_before_open hc hs

lemma loadedRepeat_germ_after {load v : Velocity} (hl : TimeCollars load) (hc : TimeCollars v)
    {t : ℝ} (ht : 1 ≤ t) :
    loadedRepeat load v =ᶠ[𝓝 t] (fun s => v (s-(⌊t⌋ : ℤ))) := by
  have hi : t - (⌊t⌋ : ℤ) ∈ Ioo (-1/4 : ℝ) (5/4) := by
    have := Int.floor_le t
    have := Int.lt_floor_add_one t
    constructor <;> linarith
  have hn : ∀ᶠ s : ℝ in 𝓝 t, s - (⌊t⌋ : ℤ) ∈ Ioo (-1/4 : ℝ) (5/4) :=
    (continuous_id.sub continuous_const).continuousAt.eventually (isOpen_Ioo.mem_nhds hi)
  filter_upwards [hn, eventually_gt_nhds (show (3 : ℝ)/4 < t by linarith)] with s hs hst
  rw [loadedRepeat_after_open hl hc hst]
  exact funext (repeatTemplate_eq hc hs)

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

lemma ElementaryField.convection {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) : ElementaryField (fun p => convection (v p)) := by
  intro k
  simp only [BalancedTransport.convection, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply ElementaryScalar.sum Finset.univ
  intro i _
  exact (hv i).mul ((hv.spaceD i) k)

lemma ElementaryField.fullInertial {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) : ElementaryField (fun p => fullInertial (v p)) :=
  fun i => ((hv.fullTimeD) i).add (hv.convection i)

lemma ElementaryField.viscous {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) : ElementaryField (fun p => viscousCoefficient (v p)) := by
  intro k
  simp only [viscousCoefficient, laplacian, Pi.neg_apply, Finset.sum_apply]
  apply ElementaryScalar.neg
  apply ElementaryScalar.sum Finset.univ
  intro i _
  exact ((hv.spaceD i).spaceD i) k

end BalancedTransport.Effectivity
end

end OAI
