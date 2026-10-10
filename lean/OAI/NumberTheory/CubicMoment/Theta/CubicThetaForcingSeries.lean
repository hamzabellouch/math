import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingSmooth

namespace OAI

/-! The actual arithmetic forcing series is locally a finite sum,
uniformly in the spectral parameter. -/
noncomputable section
open Set
namespace CubicFirstMoment

def cubicThetaForcingTerm (r : CubicThetaBottomRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  star r.phase*cubicThetaIncomingForcing s (r.height p)

def cubicThetaForcingSeries (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  ∑' r : CubicThetaBottomRow, cubicThetaForcingTerm r p s

lemma cubicThetaForcingTerm_translate (r : CubicThetaBottomRow)
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaForcingTerm r (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaForcingTerm (r.rightMul g) p s := by
  have hu : cubicThetaKubotaValue g*star (cubicThetaKubotaValue g)=1 := by
    calc
      _ = (‖cubicThetaKubotaValue g‖:ℂ)^2 := Complex.mul_conj' _
      _ = 1 := by rw [cubicThetaKubotaValue_norm]; norm_num
  rw [cubicThetaForcingTerm,cubicThetaForcingTerm,
    CubicThetaBottomRow.height_rightMul r g hp,CubicThetaBottomRow.phase_rightMul,star_mul]
  calc
    _ = (cubicThetaKubotaValue g*star (cubicThetaKubotaValue g))*
        (star r.phase*cubicThetaIncomingForcing s
          (r.height (cubicThetaMobius (cubicThetaPrincipalComplex g) p))) := by rw [hu,one_mul]
    _ = _ := by ring

theorem cubicThetaForcingSeries_automorphy (g : cubicThetaPrincipalGroup)
    {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    cubicThetaForcingSeries (cubicThetaMobius (cubicThetaPrincipalComplex g) p) s=
      cubicThetaKubotaValue g*cubicThetaForcingSeries p s := by
  unfold cubicThetaForcingSeries
  simp_rw [cubicThetaForcingTerm_translate _ g hp s]
  rw [tsum_mul_left]
  congr 1
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => cubicThetaForcingTerm r p s)

theorem cubicThetaForcingSeries_compact_sum {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K, 0<p.2) :
    ∃ S : Finset CubicThetaBottomRow, ∀ p∈K, ∀ s : ℂ,
      cubicThetaIncomingEisenstein p s=∑ r∈S, cubicThetaIncomingTerm r p s ∧
      cubicThetaForcingSeries p s=∑ r∈S, cubicThetaForcingTerm r p s := by
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hpos
  refine ⟨S,fun p hp s => ⟨?_,?_⟩⟩
  · apply tsum_eq_sum
    intro r hr
    unfold cubicThetaIncomingTerm
    rw [cubicThetaCuspCutoff_zero (hS p hp r hr).le,zero_mul]
  · apply tsum_eq_sum
    intro r hr
    unfold cubicThetaForcingTerm
    rw [cubicThetaIncomingForcing_zero s (Or.inl (hS p hp r hr)),mul_zero]

theorem cubicThetaForcingSeries_analytic {p : ℂ × ℝ} (hp : 0<p.2) (s : ℂ) :
    AnalyticAt ℂ (cubicThetaForcingSeries p) s := by
  obtain ⟨S,hS⟩ := cubicThetaForcingSeries_compact_sum isCompact_singleton
    (show ∀ q∈({p} : Set (ℂ × ℝ)), 0<q.2 from fun q hq => by
      simpa only [Set.mem_singleton_iff.mp hq] using hp)
  have he : cubicThetaForcingSeries p=(fun z => ∑ r∈S, cubicThetaForcingTerm r p z) :=
    funext (fun z => (hS p (Set.mem_singleton p) z).2)
  rw [he]
  apply Finset.analyticAt_fun_sum
  intro r _
  exact analyticAt_const.mul (cubicThetaIncomingForcing_analytic _ s)

end CubicFirstMoment

end

end OAI
