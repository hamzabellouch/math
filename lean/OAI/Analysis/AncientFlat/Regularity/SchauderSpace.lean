import OAI.Analysis.AncientFlat.Regularity.SchauderJetTime
import OAI.Analysis.AncientFlat.Regularity.SchauderLag

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff BoundedContinuousFunction SchwartzMap
namespace ParabolicSchauder
open SourceFrozenRows
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def smoothPotential (K : SchwartzMap V ℂ) (f : ℝ → (V →ᵇ ℂ)) (t : ℝ) :=
  duhamel K (fun _ _ => 1) f t
def integratedJet (K : SchwartzMap V ℂ) (f : ℝ → (V →ᵇ ℂ)) (t : ℝ) (j : ℕ) (x : V) :=
  ∫ r in Ioo 0 t, jet K (t-r) (f r) j x
lemma integrable_jet (K : SchwartzMap V ℂ) (f : ℝ → (V →ᵇ ℂ)) (hf : Continuous f)
    (α H t : ℝ) (hα : 0<α) (hα1 : α≤1) (hH : 0≤H) (ht : 0≤t)
    (hh : ∀ r ∈ Ioo 0 t, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^α)
    (j : ℕ) (hj : j≤4) (x : V) :
    IntegrableOn (fun r => jet K (t-r) (f r) j x) (Ioo 0 t) := by
  exact integrableOn_row K (fun _ _ => 1) continuous_const 1 1 zero_lt_one
    (fun _ _ => ⟨le_rfl,le_rfl⟩) 0 le_rfl (by intro r x y; simp) f hf α H t ht hα hα1 hH hh j hj x
lemma smoothPotential_contDiff (K : SchwartzMap V ℂ) (f : ℝ → (V →ᵇ ℂ)) (hf : Continuous f)
    (α H t : ℝ) (hα : 0<α) (hα1 : α≤1) (hH : 0≤H) (ht : 0≤t)
    (hh : ∀ r ∈ Ioo 0 t, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^α) :
    ContDiff ℝ 4 (smoothPotential K f t) := by
  exact contDiff_duhamel K (fun _ _ => 1) continuous_const 1 1 zero_lt_one
    (fun _ _ => ⟨le_rfl,le_rfl⟩) 0 le_rfl (by intro r x y; simp) f hf α H t ht hα hα1 hH hh
lemma derivative_smoothPotential (K : SchwartzMap V ℂ) (f : ℝ → (V →ᵇ ℂ)) (hf : Continuous f)
    (α H t : ℝ) (hα : 0<α) (hα1 : α≤1) (hH : 0≤H) (ht : 0≤t)
    (hh : ∀ r ∈ Ioo 0 t, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^α) :
    iteratedFDeriv ℝ 4 (smoothPotential K f t) = integratedJet K f t 4 := by
  exact iteratedFDeriv_duhamel K (fun _ _ => 1) continuous_const 1 1 zero_lt_one
    (fun _ _ => ⟨le_rfl,le_rfl⟩) 0 le_rfl (by intro r x y; simp) f hf α H t ht hα hα1 hH hh 4 le_rfl
lemma exists_fourth_bound (K : SchwartzMap V ℂ) (α : ℝ) (hα : 0<α) (hα1 : α≤1) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f : ℝ → (V →ᵇ ℂ)) (H t : ℝ), 0≤H → 0≤t →
      (∀ r ∈ Ioo 0 t, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^α) → ∀ x,
      ‖integratedJet K f t 4 x‖≤C*H*t^(α/4) := by
  obtain ⟨C,hC,hb⟩ := exists_jet_bound K 4 (by norm_num) α hα.le hα1
  refine ⟨C/(α/4),div_nonneg hC (by positivity),fun f H t hH ht hh x => ?_⟩
  have he := norm_integral_reverse_power (α/4) (C*H) 0 t (by positivity) ht
    (fun r => jet K (t-r) (f r) 4 x) (fun r hr => by
      convert hb (f r) H hH (hh r hr) (t-r) (sub_pos.mpr hr.2) x using 1; congr 2; norm_num; ring)
  simp only [sub_zero] at he
  exact he.trans_eq (by ring)
lemma exists_fourth_spatial_holder (K : SchwartzMap V ℂ) (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    ∃ B : ℝ, 0≤B ∧ ∀ (f : ℝ → (V →ᵇ ℂ)) (_hf : Continuous f) (H t : ℝ), 0≤H → 0≤t →
      (∀ r ∈ Ioo 0 t, ∀ x y, ‖f r x-f r y‖≤H*‖x-y‖^α) → ∀ x y,
      ‖integratedJet K f t 4 x-integratedJet K f t 4 y‖≤B*H*‖x-y‖^α := by
  obtain ⟨C,hC,hb⟩ := exists_jet_bound K 4 (by norm_num) α hα.le hα1.le
  obtain ⟨D,hD,hd⟩ := exists_jet_lipschitz K 4 α hα.le hα1.le
  let a := α/4
  let b := (α-1)/4
  have ha : 0<a := by dsimp [a]; positivity
  have hb0 : b<0 := by dsimp [b]; linarith
  have hneg : D/b≤0 := div_nonpos_of_nonneg_of_nonpos hD hb0.le
  have hpos : 0≤2*C/a := by positivity
  refine ⟨2*C/a-D/b,sub_nonneg.mpr (hneg.trans hpos),?_⟩
  intro f hf H t hH ht hh x y
  by_cases hxy : x=y
  · subst y; simp only [sub_self,norm_zero,Real.zero_rpow hα.ne',mul_zero,le_refl]
  have hq : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let q := ‖x-y‖
  have hi (x : V) := integrable_jet K f hf α H t hα hα1.le hH ht hh 4 le_rfl x
  unfold integratedJet
  rw [← integral_sub (hi x) (hi y)]
  have he := norm_integral_lag_split a b (2*C*H) (D*H*q) (q^4) t ha hb0
    (by positivity) (by positivity) (by positivity) ht
    (fun r => jet K (t-r) (f r) 4 x-jet K (t-r) (f r) 4 y)
    ((hi x).sub (hi y)).aestronglyMeasurable
    (fun r hr _ => by
      calc
        _ ≤ ‖jet K (t-r) (f r) 4 x‖+‖jet K (t-r) (f r) 4 y‖ := norm_sub_le ..
        _ ≤ C*H*(t-r)^((α-4)/4)+C*H*(t-r)^((α-4)/4) := add_le_add
          (by simpa using hb (f r) H hH (hh r hr) (t-r) (sub_pos.mpr hr.2) x)
          (by simpa using hb (f r) H hH (hh r hr) (t-r) (sub_pos.mpr hr.2) y)
        _ = _ := by rw [show (α-4)/4=a-1 by dsimp [a]; ring]; ring)
    (fun r hr _ => by
      convert hd (f r) H hH (hh r hr) (t-r) (sub_pos.mpr hr.2) x y using 1
      simp only [b,q,Nat.cast_ofNat]; rw [show (α-(4+1))/4=(α-1)/4-1 by ring]; ring)
  have hpa : (q^4)^a=q^α := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hq)]
    congr 1; dsimp [a]; ring
  have hpb : q*(q^4)^b=q^α := by
    calc
      _ = q^1*q^(4*b) := by rw [Real.rpow_one,← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hq)]; norm_num; exact Or.inl rfl
      _ = q^(1+4*b) := (Real.rpow_add hq 1 (4*b)).symm
      _ = _ := by congr 1; dsimp [b]; ring
  apply he.trans_eq
  rw [hpa]
  calc
    _ = (2*C/a)*H*q^α-(D/b)*H*(q*(q^4)^b) := by ring
    _ = _ := by rw [hpb]; ring
end ParabolicSchauder

end

end OAI
