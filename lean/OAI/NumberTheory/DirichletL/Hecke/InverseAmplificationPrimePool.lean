import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationAggregate
import OAI.NumberTheory.DirichletL.Moments.PrimePool

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def RawScaleEnergy (data : RowData) (W : ℝ→ℂ) (U D V E : ℝ) : Prop :=
  ∀ R : Finset NonzeroElement,
    (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
    ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true W (Real.exp l) 0 0‖^2≤E

def typedPrimePool (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) : Finset PrimeIdeal :=
  (CenteredMomentPrimePool.primePool M H S a b x).subtype Prime

theorem typedPrimePool_card (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) :
    (typedPrimePool M H S a b x).card=
      (CenteredMomentPrimePool.primePool M H S a b x).card := by
  rw [typedPrimePool,Finset.card_subtype]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro P hP
  exact ((PNT.AnnularPrimeMass.mem_annularPrimeIdeals _ _ _ _ _).mp
    (Finset.mem_sdiff.mp hP).1).2.1

theorem typedPrimePool_norm (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) (ha : 0≤a) (hab : a≤b) (hx : 0<x)
    (P : PrimeIdeal) (hP : P∈typedPrimePool M H S a b x) :
    (P.val.absNorm : ℝ)≤x*b := by
  have hh := Finset.mem_subtype.mp hP
  exact (PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals ha hab hx
    (Finset.mem_sdiff.mp hh).1).2

theorem eventually_fixed_ray_amplification
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb D U E : ℝ),
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      0<D → (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      RawScaleEnergy data W U D (x*b) E →
      RawScaleEnergy data (scaleProfile W) U D (x*b) E →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2)≤
        4*(1+2*Real.log (x*b))*E*Real.log x/(c*x) := by
  obtain ⟨c,hc,hcard⟩ := CenteredMomentPrimePool.eventually_primePool_card M H hH S
    φ hφ hφc hφp hφ0 hφne a b B ha hab hB hφs hφB
  have hb : 0<b := ha.trans_le hab
  refine ⟨c,hc,?_⟩
  filter_upwards [hcard,eventually_gt_atTop (1 : ℝ),eventually_ge_atTop (1/b)] with x hcard hx hxB
  intro data rows W wa wb D U E hwa hwb hWs hW hD hrows hraw0 hraw1
  have hx0 : 0<x := zero_lt_one.trans hx
  have hxblog : 1≤x*b := (div_le_iff₀ hb).mp hxB
  have hlog : 0<Real.log x := Real.log_pos hx
  have hc' : c*x/Real.log x≤((typedPrimePool M H S a b x).card : ℝ) := by
    rw [typedPrimePool_card]
    exact hcard
  have havg := averaged_energy data rows (typedPrimePool M H S a b x) W wa wb hwa hwb
    hWs hW D U (x*b) E hD hxblog hrows
    (fun P hP => typedPrimePool_norm M H S a b x ha.le hab hx0 P hP) hraw0 hraw1
  have hsum : 0≤∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := (mul_le_mul_of_nonneg_right hc' hsum).trans havg
  apply (le_div_iff₀ (mul_pos hc hx0)).mpr
  calc
    _ = (c*x/Real.log x*(∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2))*Real.log x := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hh hlog.le

end SevenEighths.HeckeInverseAmplification

end

end OAI
