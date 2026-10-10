import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyJets
import OAI.MathematicalPhysics.Transonic.Shooting.ShootingField
import OAI.MathematicalPhysics.Transonic.Shooting.ClampedFamily
import OAI.MathematicalPhysics.Transonic.Shooting.ClampedComparison

namespace OAI

section
noncomputable section

namespace SepticProfile.EulerFamily
open Set SourceFamily RegularContinuation ShootingParameters

def field (p : ℝ×(ℝ×ℝ)) : ℝ :=
  EulerContinuation.N (kappa p.2.1) p.1 p.2.2/EulerContinuation.D (sigma p.2.1) p.1 p.2.2

lemma field_contDiffOn {a b cap : ℝ} (ha : 0≤a) (hb : b≤5/6) (hcap : cap<1) :
    ContDiffOn ℝ 1 field (Icc a b ×ˢ (Icc leftEnd rightEnd ×ˢ Icc 0 cap)) := by
  let S := Icc a b ×ˢ (Icc leftEnd rightEnd ×ˢ Icc 0 cap)
  have hpar : MapsTo (fun p : ℝ×(ℝ×ℝ) => p.2.1) S (Icc leftEnd rightEnd) := fun p hp => hp.2.1
  have hs := sigma_contDiffOn.comp (contDiffOn_snd.fst) hpar
  have hk := kappa_contDiffOn.comp (contDiffOn_snd.fst) hpar
  have hN : ContDiffOn ℝ 1 (fun p : ℝ×(ℝ×ℝ) => EulerContinuation.N (kappa p.2.1) p.1 p.2.2) S := by
    unfold EulerContinuation.N
    fun_prop
  have hD : ContDiffOn ℝ 1 (fun p : ℝ×(ℝ×ℝ) => EulerContinuation.D (sigma p.2.1) p.1 p.2.2) S := by
    unfold EulerContinuation.D
    fun_prop
  exact hN.div hD (fun p hp => ne_of_gt (EulerContinuation.D_pos
    (by linarith [(sigma_shooting_bounds hp.2.1).2])
    ⟨ha.trans hp.1.1,hp.1.2.trans hb⟩ ⟨hp.2.2.1,hp.2.2.2.trans_lt hcap⟩))

theorem exists_family {a : ℝ} (ha : 0<a) (hab : a≤5/6)
    (seed : Parameter → ℝ) (hseed : Continuous seed) :
    ∃ u : Parameter → ℝ → ℝ,
      Continuous (fun p : Parameter × ↥(Icc a (5/6)) => u p.1 p.2) ∧
      (∀ t, u t a=seed t) ∧
      ∀ t x, x ∈ Icc a (5/6) → HasDerivWithinAt (u t)
        (EulerContinuation.N (kap t) x (clamp 0 (1-a/1000) (u t x))/
          EulerContinuation.D (sig t) x (clamp 0 (1-a/1000) (u t x))) (Icc a (5/6)) x := by
  exact exists_continuous_clamped_family hab
    (by norm_num [leftEnd,rightEnd]) (by linarith : (0:ℝ)≤1-a/1000)
    (field_contDiffOn ha.le le_rfl (by linarith))
    (fun a:Parameter => a.val) seed continuous_subtype_val hseed (fun a => a.property)

theorem polynomial_trap {sigma kappa a : ℝ} (hsig : sigma<1) (ha : 0<a) (hab : a≤5/6)
    {u : ℝ → ℝ} (hud : ∀ t ∈ Icc a (5/6), HasDerivWithinAt u
      (EulerContinuation.N kappa t (clamp 0 (1-a/1000) (u t))/
        EulerContinuation.D sigma t (clamp 0 (1-a/1000) (u t))) (Icc a (5/6)) t)
    (p q : Polynomial ℝ)
    (hrangep : ∀ t ∈ Icc (0:ℝ) (5/6), 1-t/50≤p.eval t ∧ p.eval t≤1-t/500)
    (hrangeq : ∀ t ∈ Icc (0:ℝ) (5/6), 1-t/50≤q.eval t ∧ q.eval t≤1-t/500)
    (hresp : ∀ t ∈ Ioc (0:ℝ) (5/6), EulerFormal.profileResidual sigma kappa (3/5) (1/500) (fun x => p.eval x) t<0)
    (hresq : ∀ t ∈ Ioc (0:ℝ) (5/6), 0<EulerFormal.profileResidual sigma kappa (3/5) (1/500) (fun x => q.eval x) t)
    (hinit : u a ∈ Icc (p.eval a) (q.eval a)) :
    ∀ t ∈ Icc a (5/6), u t ∈ Icc (p.eval t) (q.eval t) := by
  have ht0 {t : ℝ} (ht : t ∈ Icc a (5/6)) : t ∈ Icc 0 (5/6) := ⟨ha.le.trans ht.1,ht.2⟩
  have htp {t : ℝ} (ht : t ∈ Icc a (5/6)) : t ∈ Ioc 0 (5/6) := ⟨ha.trans_le ht.1,ht.2⟩
  have hpr (t : ℝ) (ht : t ∈ Icc a (5/6)) : p.eval t ∈ Icc 0 (1-a/1000) := by
    have hh := hrangep t (ht0 ht)
    constructor <;> linarith [ht.1,ht.2]
  have hqr (t : ℝ) (ht : t ∈ Icc a (5/6)) : q.eval t ∈ Icc 0 (1-a/1000) := by
    have hh := hrangeq t (ht0 ht)
    constructor <;> linarith [ht.1,ht.2]
  apply (clamped_stays_between_strict (f := fun p:ℝ×ℝ => EulerContinuation.N kappa p.1 p.2/EulerContinuation.D sigma p.1 p.2) (fun t ht => (hud t ht).continuousWithinAt) hud
    (fun t => p.eval t) (fun t => q.eval t)
    (fun t => deriv (fun x => p.eval x) t) (fun t => deriv (fun x => q.eval x) t)
    (fun t _ => p.differentiableAt.hasDerivAt) (fun t _ => q.differentiableAt.hasDerivAt)
    hpr hqr ?_ ?_ hinit).1
  · intro t ht
    apply (lt_div_iff₀ (EulerContinuation.D_pos hsig (ht0 ht)
      ⟨(hpr t ht).1,lt_of_le_of_lt (hpr t ht).2 (by linarith)⟩)).mpr
    have hh := hresp t (htp ht)
    rw [EulerContinuation.residual_eq] at hh
    nlinarith only [hh]
  · intro t ht
    apply (div_lt_iff₀ (EulerContinuation.D_pos hsig (ht0 ht)
      ⟨(hqr t ht).1,lt_of_le_of_lt (hqr t ht).2 (by linarith)⟩)).mpr
    have hh := hresq t (htp ht)
    rw [EulerContinuation.residual_eq] at hh
    nlinarith only [hh]

end SepticProfile.EulerFamily

end
end

end OAI
