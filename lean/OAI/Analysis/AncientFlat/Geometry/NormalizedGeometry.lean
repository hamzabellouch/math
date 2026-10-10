import OAI.Analysis.AncientFlat.Weighted.WeightedScaling
import OAI.Analysis.AncientFlat.Evolution.CoreProfile
import OAI.Analysis.AncientFlat.Geometry.AnnularCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace FlatWeighted
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def CoreCenter (p : V × ℝ) : Prop := ‖p.1‖≤1 ∧ p.2=-1
def AnnularCenter (p : V × ℝ) : Prop := ‖p.1‖=1 ∧ -1≤p.2 ∧ p.2<0
omit [FiniteDimensional ℝ V] in
lemma normalized_center (p : V × ℝ) (hp : p.2<0) :
    ∃ r : ℝ, 0<r ∧ ∃ q : V × ℝ, scale r q=p ∧ (CoreCenter q ∨ AnnularCenter q) := by
  let τ : ℝ := (-p.2)^((1:ℝ)/4)
  have hτ : 0<τ := Real.rpow_pos_of_pos (neg_pos.mpr hp) _
  have hτ4 : τ^4=-p.2 := by
    dsimp [τ]
    rw [←Real.rpow_natCast,←Real.rpow_mul (neg_pos.mpr hp).le]
    norm_num
  by_cases hx : ‖p.1‖≤τ
  · refine ⟨τ,hτ,(τ⁻¹ • p.1,-1),?_,Or.inl ?_⟩
    · simp only [scale,smul_smul,mul_inv_cancel₀ hτ.ne',one_smul,hτ4,mul_neg_one,neg_neg,Prod.mk.eta]
    · constructor
      · simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hτ)]
        exact (inv_mul_le_iff₀ hτ).mpr (by simpa using hx)
      · rfl
  · have hr : 0<‖p.1‖ := hτ.trans (not_le.mp hx)
    refine ⟨‖p.1‖,hr,(‖p.1‖⁻¹ • p.1,p.2/‖p.1‖^4),?_,Or.inr ?_⟩
    · simp only [scale,smul_smul,mul_inv_cancel₀ hr.ne',one_smul,mul_div_cancel₀ _ (pow_ne_zero 4 hr.ne'),Prod.mk.eta]
    · refine ⟨?_,?_,div_neg_of_neg_of_pos hp (pow_pos hr _)⟩
      · simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),inv_mul_cancel₀ hr.ne']
      · apply (le_div_iff₀ (pow_pos hr 4)).mpr
        have hh := pow_le_pow_left₀ hτ.le (not_le.mp hx).le 4
        rw [hτ4] at hh
        linarith
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma normalized_sigma {p : V × ℝ} (hp : CoreCenter p ∨ AnnularCenter p) :
    p.2<0 ∧ 1 ≤ sigma p ∧ sigma p≤2 := by
  have ht : p.2<0 := by
    rcases hp with h|h
    · rw [h.2]; norm_num
    · exact h.2.2
  have hs : 0≤Real.sqrt (-p.2) := Real.sqrt_nonneg _
  have hsq : ‖p.1‖^2+Real.sqrt (-p.2)≥1 ∧ ‖p.1‖^2+Real.sqrt (-p.2)≤4 := by
    rcases hp with h|h
    · rw [h.2]
      norm_num
      nlinarith [norm_nonneg p.1,h.1]
    · rw [h.1]
      have hb : Real.sqrt (-p.2)≤1 := (Real.sqrt_le_one).mpr (by linarith [h.2.1])
      constructor <;> nlinarith
  refine ⟨ht,?_,?_⟩
  · unfold sigma
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; exact hsq.1)
  · unfold sigma
    exact (Real.sqrt_le_left (by norm_num)).mpr (by norm_num; exact hsq.2)
lemma normalized_chart_maps {a : ℝ} (ha : 0<a) (ha1 : a≤1/16) (p : V × ℝ)
    (hp : CoreCenter p ∨ AnnularCenter p) :
    (CoreCenter p → MapsTo (chart p) (localDomain a p) ParabolicCore.inner) ∧
    (AnnularCenter p → MapsTo (chart p) (localDomain a p) ParabolicAnnular.inner) := by
  obtain ⟨ht,hs1,hs2⟩ := normalized_sigma hp
  have hs := sigma_pos p ht
  have hsp : ∀ q∈localDomain a p, ‖sigma p • q.1‖<1/8 := by
    intro q hq
    rw [norm_smul,Real.norm_of_nonneg hs.le]
    have hqa : ‖q.1‖<1/16 := hq.1.trans_le ha1
    nlinarith [norm_nonneg q.1]
  have htm : ∀ q∈localDomain a p, |sigma p^4*q.2|<1/2 := by
    intro q hq
    have hqa : |q.2|<a^4 := abs_lt.mpr ⟨hq.2.1,hq.2.2.1⟩
    have ha4 : a^4≤(1:ℝ)/65536 := by
      have hh := pow_le_pow_left₀ ha.le ha1 4
      norm_num at hh
      exact hh
    have hs4 : sigma p^4≤16 := by
      have hh := pow_le_pow_left₀ hs.le hs2 4
      norm_num at hh
      exact hh
    rw [abs_mul,abs_of_nonneg (pow_nonneg hs.le 4)]
    nlinarith [abs_nonneg q.2,pow_nonneg hs.le 4]
  constructor
  · intro hc q hq
    have hn := (norm_add_le p.1 (sigma p • q.1)).trans_lt (by linarith [hsp q hq,hc.1] : ‖p.1‖+‖sigma p • q.1‖<2)
    have hu := abs_lt.mp (htm q hq)
    exact ⟨hn,by dsimp [chart]; rw [hc.2]; linarith,by dsimp [chart]; rw [hc.2]; linarith⟩
  · intro hc q hq
    have hn : ‖p.1+sigma p • q.1‖<5/4 := (norm_add_le _ _).trans_lt (by linarith [hsp q hq,hc.1])
    have hlo : 3/4<‖p.1+sigma p • q.1‖ := by
      have hh := norm_sub_norm_le p.1 (-(sigma p • q.1))
      simp only [sub_neg_eq_add,norm_neg] at hh
      linarith [hsp q hq,hc.1]
    have hu := abs_lt.mp (htm q hq)
    exact ⟨hlo,hn,by dsimp [chart]; linarith [hc.2.1],hq.2.2.2⟩
end FlatWeighted

end

end OAI
