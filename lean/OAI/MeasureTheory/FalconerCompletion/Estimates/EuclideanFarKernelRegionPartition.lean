import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.FarChildMaximum
import OAI.MeasureTheory.FalconerCompletion.Graphs.SphereAxisIntegralNormBoundGeneral

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff

theorem euclideanFarKernelND_region_partition {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (v : ℝ)
    (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (a : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
    {C : ℝ} (hC : 0≤C)
    (hbd : ∀ᵐ x ∂ρ.prod ρ, ∀ w, ‖w‖=1 → ‖b x w‖≤C)
    (hcd : ∀ᵐ x ∂κ.prod κ, ∀ w, ‖w‖=1 → ‖c x w‖≤C) :
    (∫ x in (⋃ pq∈P.product Q, gridPairSetND a pq.1 ×ˢ gridPairSetND a pq.2),
      euclideanFarKernelND Ψ v b c x ∂(ρ.prod ρ).prod (κ.prod κ)) =
      ∑ pq∈P.product Q, ∫ x, euclideanFarKernelND Ψ v b c x
        ∂(gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2) := by
  apply gridPairMeasureND_integral_quad_partition
  apply euclideanFarKernelND_integrable hΨ hs v b c hb hc _ hC
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbd,
    Measure.quasiMeasurePreserving_snd.ae hcd] with x hx hy
  exact ⟨hx,hy⟩

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar

lemma far_dyadic_prefactorsND (d a b v : ℝ) :
    (2:ℝ)^(d*(v-a))*(2:ℝ)^(-(d-1)*(v-b))*(2:ℝ)^(-(v-b)) =
      (2:ℝ)^(d*(b-a)) := by
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

theorem far_profile_cancellationND (N : ℕ) (hN : 0<N) (d a b v ma mb loss : ℝ) :
    let R : ℝ := (2:ℝ)^N
    let Aa : ℝ := ma-d*a/(2*(N:ℝ))
    let Ab : ℝ := mb-d*b/(2*(N:ℝ))
    ((2:ℝ)^(d*(v-a))/(R^(-ma))^4)*
      (2:ℝ)^(-(d-1)*(v-b))*(R^(-mb))^4*(2:ℝ)^(-(v-b))*R^(2*(mb-ma)+loss) =
        R^(-2*(Ab-Aa)+loss) := by
  dsimp only
  let R : ℝ := (2:ℝ)^N
  have hR : 0<R := by positivity
  have hN' : (N:ℝ)≠0 := by positivity
  have hfreq : (2:ℝ)^(d*(b-a))=R^(d*(b-a)/(N:ℝ)) := by
    dsimp [R]
    rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    field_simp
  change ((2:ℝ)^(d*(v-a))/(R^(-ma))^4)*
      (2:ℝ)^(-(d-1)*(v-b))*(R^(-mb))^4*(2:ℝ)^(-(v-b))*R^(2*(mb-ma)+loss) = _
  calc
    _ = ((2:ℝ)^(d*(v-a))*(2:ℝ)^(-(d-1)*(v-b))*(2:ℝ)^(-(v-b)))*
        ((R^(-mb))^4/(R^(-ma))^4)*R^(2*(mb-ma)+loss) := by ring
    _ = R^(d*(b-a)/(N:ℝ))*((R^(-mb))^4/(R^(-ma))^4)*R^(2*(mb-ma)+loss) := by
      rw [far_dyadic_prefactorsND,hfreq]
    _ = R^(-2*((mb-d*b/(2*(N:ℝ)))-(ma-d*a/(2*(N:ℝ))))+loss) := by
      rw [← Real.rpow_mul_natCast hR.le,← Real.rpow_mul_natCast hR.le,
        ← Real.rpow_sub hR,← Real.rpow_add hR,← Real.rpow_add hR]
      congr 1
      push_cast
      ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Metric

theorem far_actual_label_normalizationND {d : ℕ} (N : ℕ) (hN : 0<N)
    (a : ℝ) (b : ℕ) (v ma mb err : ℝ) {K : ℝ} (hK : 0≤K)
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    (A B : Finset (Fin d → ℤ)) (X Y : Set (EuclideanSpace ℝ (Fin d)))
    (hA : ∀ p∈P, p.1∈A) (hB : ∀ q∈Q, q.1∈B)
    (hP : ∀ p∈P, farSeparatedGridND b K p.1 p.2)
    (hQ : ∀ q∈Q, farSeparatedGridND b K q.1 q.2)
    (hs₁ : ∀ i∈A, ambientGridCell b i⊆X) (hs₂ : ∀ j∈B, ambientGridCell b j⊆Y)
    (hl₁ : ∀ i∈A, ((2:ℝ)^N)^(-mb-err)≤(μ (ambientGridCell b i)).toReal)
    (hl₂ : ∀ j∈B, ((2:ℝ)^N)^(-mb-err)≤(ν (ambientGridCell b j)).toReal)
    (hu₁ : (μ X).toReal≤((2:ℝ)^N)^(-ma+err))
    (hu₂ : (ν Y).toReal≤((2:ℝ)^N)^(-ma+err)) :
    let R : ℝ := (2:ℝ)^N
    let Aa : ℝ := ma-d*a/(2*(N:ℝ))
    let Ab : ℝ := mb-d*b/(2*(N:ℝ))
    ((2:ℝ)^((d:ℝ)*(v-a))/(R^(-ma))^4)*
      (2:ℝ)^(-((d:ℝ)-1)*(v-b))*(R^(-mb))^4*(2:ℝ)^(-(v-b))*((P.product Q).card:ℝ) ≤
        (8*K+5)^(2*d)*R^(-2*(Ab-Aa)+4*err) := by
  dsimp only
  have hR : 0<(2:ℝ)^N := by positivity
  have hcard := far_profile_quadruple_cardND b hK μ ν P Q A B X Y hA hB hP hQ hs₁ hs₂ hR hl₁ hl₂ hu₁ hu₂
  have hexp : (mb-ma)+(mb-ma)+2*(err+err)=2*(mb-ma)+4*err := by ring
  rw [hexp] at hcard
  calc
    _ ≤ ((2:ℝ)^((d:ℝ)*(v-a))/(((2:ℝ)^N)^(-ma))^4)*
        (2:ℝ)^(-((d:ℝ)-1)*(v-b))*(((2:ℝ)^N)^(-mb))^4*(2:ℝ)^(-(v-b))*
        ((8*K+5)^(2*d)*((2:ℝ)^N)^(2*(mb-ma)+4*err)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (8*K+5)^(2*d)*
        (((2:ℝ)^((d:ℝ)*(v-a))/(((2:ℝ)^N)^(-ma))^4)*
        (2:ℝ)^(-((d:ℝ)-1)*(v-b))*(((2:ℝ)^N)^(-mb))^4*(2:ℝ)^(-(v-b))*
        ((2:ℝ)^N)^(2*(mb-ma)+4*err)) := by ring
    _ = _ := by rw [far_profile_cancellationND N hN d a b v ma mb (4*err)]

theorem far_actual_error_normalizationND {d : ℕ} (N : ℕ) (_hN : 0<N)
    {a v ma err : ℝ} (hav : v-a≤N)
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (X Y : Set (EuclideanSpace ℝ (Fin d)))
    (hu₁ : (μ X).toReal≤((2:ℝ)^N)^(-ma+err))
    (hu₂ : (ν Y).toReal≤((2:ℝ)^N)^(-ma+err)) :
    ((2:ℝ)^((d:ℝ)*(v-a))/(((2:ℝ)^N)^(-ma))^4)*(μ X).toReal^2*(ν Y).toReal^2 ≤
      ((2:ℝ)^N)^((d:ℝ)+4*err) := by
  have hR : 0<(2:ℝ)^N := by positivity
  have hmass : (μ X).toReal^2*(ν Y).toReal^2 ≤ (((2:ℝ)^N)^(-ma+err))^4 := by
    have h₁ := pow_le_pow_left₀ ENNReal.toReal_nonneg hu₁ 2
    have h₂ := pow_le_pow_left₀ ENNReal.toReal_nonneg hu₂ 2
    have hh := mul_le_mul h₁ h₂ (sq_nonneg _) (sq_nonneg _)
    simpa only [← pow_add] using hh
  have hfreq : (2:ℝ)^((d:ℝ)*(v-a))≤((2:ℝ)^N)^(d:ℝ) := by
    rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    nlinarith [show (0:ℝ)≤d by positivity]
  calc
    _ = ((2:ℝ)^((d:ℝ)*(v-a))/(((2:ℝ)^N)^(-ma))^4)*((μ X).toReal^2*(ν Y).toReal^2) := by ring
    _ ≤ ((2:ℝ)^((d:ℝ)*(v-a))/(((2:ℝ)^N)^(-ma))^4)*(((2:ℝ)^N)^(-ma+err))^4 :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^N)^(4*err) := by
      rw [← Real.rpow_mul_natCast hR.le,← Real.rpow_mul_natCast hR.le]
      have he : ((2:ℝ)^N)^((-ma+err)*(4:ℕ))/((2:ℝ)^N)^(-ma*(4:ℕ))=((2:ℝ)^N)^(4*err) := by
        rw [← Real.rpow_sub hR]
        congr 1; push_cast; ring
      rw [div_mul_eq_mul_div,mul_div_assoc,he]
    _ ≤ ((2:ℝ)^N)^(d:ℝ)*((2:ℝ)^N)^(4*err) :=
      mul_le_mul_of_nonneg_right hfreq (by positivity)
    _ = _ := by rw [← Real.rpow_add hR]

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology ENNReal
attribute [local instance] Classical.propDecidable

theorem euclidean_far_normalized_sumND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ : ℝ} (hθ : 0<θ) (err T K : ℝ) (hK : 0≤K) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (N : ℕ), 0<N → R=(2:ℝ)^N →
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (a : ℝ) (k : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
        (L₁ L₂ : Finset (Fin (n+1) → ℤ)) (X Y : Set (EuclideanSpace ℝ (Fin (n+1))))
        (v ma mb A : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      v-a≤N → 1≤A → A≤R^2 →
      (∀ p∈P, ambientGridCell k p.1⊆X ∧ ambientGridCell k p.2⊆X) →
      (∀ q∈Q, ambientGridCell k q.1⊆Y ∧ ambientGridCell k q.2⊆Y) →
      (∀ p∈P, p.1∈L₁) → (∀ q∈Q, q.1∈L₂) →
      (∀ p∈P, farSeparatedGridND k K p.1 p.2) → (∀ q∈Q, farSeparatedGridND k K q.1 q.2) →
      (∀ i∈L₁, ambientGridCell k i⊆X) → (∀ j∈L₂, ambientGridCell k j⊆Y) →
      (∀ i∈L₁, R^(-mb-err)≤(ρ (ambientGridCell k i)).toReal) →
      (∀ j∈L₂, R^(-mb-err)≤(κ (ambientGridCell k j)).toReal) →
      (ρ X).toReal≤R^(-ma+err) → (κ Y).toReal≤R^(-ma+err) →
      MeasurableSet {x | euclideanPairDirectionND x∈U x} →
      MeasurableSet {x | euclideanPairDirectionND x∈W x} →
      (∀ p∈P, ∀ᵐ x ∂gridPairMeasureND ρ k p,
        (2:ℝ)^(-(k:ℝ))/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (b x) ∧
        (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*A^j)) →
      (∀ q∈Q, ∀ᵐ x ∂gridPairMeasureND κ k q,
        (2:ℝ)^(-(k:ℝ))/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (c x) ∧
        (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*A^j)) →
      ((2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4)*
        ‖∑ pq∈P.product Q, ∫ x, euclideanFarKernelND Ψ v b c x
          ∂(gridPairMeasureND ρ k pq.1).prod (gridPairMeasureND κ k pq.2)‖ ≤
        H*R^(-2*((mb-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k P Q v (R^(-mb)) U W).toReal+R^(-T) := by
  obtain ⟨J,H,hH,hh⟩ := euclidean_far_finite_sumND (n := n) hΨ hs C hC hθ 0 (T+(n+1:ℝ)+4*err)
  refine ⟨J,H*binKernelConstant.toReal*(8*K+5)^(2*(n+1)),by positivity,?_⟩
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with R hh hR
  intro N hN hRN ρ κ _ _ a k P Q L₁ L₂ X Y v ma mb A b c U W hav hA hAup hPx hQy
    hL₁ hL₂ hP hQ hs₁ hs₂ hl₁ hl₂ hu₁ hu₂ hU hW hb hc
  have hsum := hh ρ κ k P Q X Y v (R^(-mb)) A b c U W
    (by positivity) hA hAup hPx hQy hU hW hb hc
  simp only [Real.rpow_zero,one_mul] at hsum
  have hlabel := far_actual_label_normalizationND N hN a k v ma mb err hK
    ρ κ P Q L₁ L₂ X Y hL₁ hL₂ hP hQ hs₁ hs₂
    (by simpa only [← hRN] using hl₁) (by simpa only [← hRN] using hl₂)
    (by simpa only [← hRN] using hu₁) (by simpa only [← hRN] using hu₂)
  dsimp only at hlabel
  simp only [← hRN,Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hlabel
  have hmass := far_actual_error_normalizationND N hN hav ρ κ X Y
    (by simpa only [← hRN] using hu₁) (by simpa only [← hRN] using hu₂)
  simp only [← hRN,Nat.cast_add,Nat.cast_one] at hmass
  let F := (2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4
  let D := (farChildMaximumND ρ κ k P Q v (R^(-mb)) U W).toReal
  have hF : 0≤F := by dsimp [F]; positivity
  have hD : 0≤D := ENNReal.toReal_nonneg
  have he : (F*(ρ X).toReal^2*(κ Y).toReal^2)*R^(-(T+(n+1:ℝ)+4*err))≤R^(-T) := by
    calc
      _ ≤ R^((n+1:ℝ)+4*err)*R^(-(T+(n+1:ℝ)+4*err)) :=
        mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring
  calc
    _ ≤ F*((H*(2:ℝ)^(-(n:ℝ)*(v-k)))*
        (binKernelConstant.toReal*((R^(-mb))^4*(2:ℝ)^(-(v-k)))*((P.product Q).card:ℝ)*D)+
        (ρ X).toReal^2*(κ Y).toReal^2*R^(-(T+(n+1:ℝ)+4*err))) :=
      mul_le_mul_of_nonneg_left hsum hF
    _ = (H*binKernelConstant.toReal*D)*
        (F*(2:ℝ)^(-(n:ℝ)*(v-k))*(R^(-mb))^4*(2:ℝ)^(-(v-k))*((P.product Q).card:ℝ))+
        (F*(ρ X).toReal^2*(κ Y).toReal^2)*R^(-(T+(n+1:ℝ)+4*err)) := by ring
    _ ≤ (H*binKernelConstant.toReal*D)*
        ((8*K+5)^(2*(n+1))*R^(-2*((mb-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err))+R^(-T) :=
      add_le_add (mul_le_mul_of_nonneg_left hlabel (by positivity)) he
    _ = _ := by dsimp [D]; ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Metric

theorem farSeparatedGridND_all_lengths {d b : ℕ} {K : ℝ}
    (hK : 32*(d+1:ℝ)≤K) {X Y : Fin d → ℤ}
    (hXY : farSeparatedGridND b K X Y) {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x∈ambientGridCell b X) (hy : y∈ambientGridCell b Y) :
    K/(16*(2:ℝ)^b)≤dist x y ∧ dist x y≤8*K/(2:ℝ)^b := by
  have hp : 0<(2:ℝ)^b := by positivity
  have hcx := ambientGridCell_dist_le hx (ambientGridCenter_mem b X)
  have hcy := ambientGridCell_dist_le hy (ambientGridCenter_mem b Y)
  have hxy := dist_triangle4 x (ambientGridCenter b X) (ambientGridCenter b Y) y
  have hcc := dist_triangle4 (ambientGridCenter b X) x y (ambientGridCenter b Y)
  rw [dist_comm x (ambientGridCenter b X)] at hxy
  rw [dist_comm y (ambientGridCenter b Y)] at hcc
  have hk := div_le_div_of_nonneg_right hK hp.le
  have hk' : 32*((d+1:ℝ)/(2:ℝ)^b)≤K/(2:ℝ)^b := by simpa only [mul_div_assoc] using hk
  have he₁ : K/(8*(2:ℝ)^b)=(K/(2:ℝ)^b)/8 := by ring
  have he₂ : K/(16*(2:ℝ)^b)=(K/(2:ℝ)^b)/16 := by ring
  have he₃ : 4*K/(2:ℝ)^b=4*(K/(2:ℝ)^b) := by ring
  have he₄ : 8*K/(2:ℝ)^b=8*(K/(2:ℝ)^b) := by ring
  rcases hXY with ⟨hlo,hhi⟩
  rw [he₁] at hlo
  rw [he₃] at hhi
  rw [he₂,he₄]
  constructor <;> linarith

lemma farSeparatedGridND_ae_lower {d b : ℕ} {K : ℝ}
    (hK : 32*(d+1:ℝ)≤K) (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (p : (Fin d → ℤ) × (Fin d → ℤ)) (hp : farSeparatedGridND b K p.1 p.2) :
    ∀ᵐ x ∂gridPairMeasureND ρ b p, (2:ℝ)^(-(b:ℝ))/4≤dist x.1 x.2 := by
  filter_upwards [ae_restrict_mem (μ := ρ.prod ρ) (gridPairSetND_measurable b p)] with x hx
  have hh := (farSeparatedGridND_all_lengths hK hp hx.1 hx.2).1
  have hK' : 4≤K := by have hd : (0:ℝ)≤d := Nat.cast_nonneg d; linarith
  have hlow : (2:ℝ)^(-(b:ℝ))/4≤K/(16*(2:ℝ)^b) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
    apply (le_div_iff₀ (by positivity : 0<16*(2:ℝ)^b)).mpr
    have hpw : (2:ℝ)^b≠0 := by positivity
    field_simp
    linarith
  exact hlow.trans hh

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff

theorem euclideanFarKernelND_local_partition {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (v : ℝ)
    (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (a : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
    {C : ℝ} (hC : 0≤C)
    (hbd : ∀ p∈P, ∀ᵐ x ∂gridPairMeasureND ρ a p, ∀ w, ‖w‖=1 → ‖b x w‖≤C)
    (hcd : ∀ q∈Q, ∀ᵐ x ∂gridPairMeasureND κ a q, ∀ w, ‖w‖=1 → ‖c x w‖≤C) :
    (∫ x in (⋃ pq∈P.product Q, gridPairSetND a pq.1 ×ˢ gridPairSetND a pq.2),
      euclideanFarKernelND Ψ v b c x ∂(ρ.prod ρ).prod (κ.prod κ)) =
      ∑ pq∈P.product Q, ∫ x, euclideanFarKernelND Ψ v b c x
        ∂(gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2) := by
  have hd : ((P.product Q) : Set (((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)) ×
      ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))).PairwiseDisjoint
      (fun pq => gridPairSetND a pq.1 ×ˢ gridPairSetND a pq.2) := by
    intro p _ q _ hpq
    apply Set.disjoint_left.mpr
    intro z hp hq
    apply hpq
    apply Prod.ext
    · by_contra hn
      exact Set.disjoint_left.mp (gridPairSetND_disjoint hn) hp.1 hq.1
    · by_contra hn
      exact Set.disjoint_left.mp (gridPairSetND_disjoint hn) hp.2 hq.2
  have hi : ∀ pq∈P.product Q, IntegrableOn (euclideanFarKernelND Ψ v b c)
      (gridPairSetND a pq.1 ×ˢ gridPairSetND a pq.2) ((ρ.prod ρ).prod (κ.prod κ)) := by
    intro pq hpq
    rw [IntegrableOn,← Measure.prod_restrict]
    change Integrable _ ((gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2))
    apply euclideanFarKernelND_integrable hΨ hs v b c hb hc _ hC
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hbd _ (Finset.mem_product.mp hpq).1),
      Measure.quasiMeasurePreserving_snd.ae (hcd _ (Finset.mem_product.mp hpq).2)] with x hx hy
    exact ⟨hx,hy⟩
  rw [integral_biUnion_finset _ (fun pq _ => (gridPairSetND_measurable a pq.1).prod
    (gridPairSetND_measurable a pq.2)) hd hi]
  apply Finset.sum_congr rfl
  intro pq _
  rw [← Measure.prod_restrict]
  rfl

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
