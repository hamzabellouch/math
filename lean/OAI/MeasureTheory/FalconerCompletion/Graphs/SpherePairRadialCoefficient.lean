import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.RadialStationaryProfile
import OAI.MeasureTheory.FalconerCompletion.Fourier.SignedDistanceFrequency
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereShift

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι]

noncomputable def spherePairRadialCoefficientND (Ψ : ℝ → ℝ) (n : ℕ)
    (B : OrthonormalBasis ι ℝ V) (p q : Polynomial ℂ) (j k : ℕ)
    (b c : SmoothFunctionND V) (w z : V) (Λ Μ s : ℝ) : ℂ :=
  (((Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2):ℝ):ℂ) *
    (normalizedDifferentialND B p j b Λ w * star (normalizedDifferentialND B q k c Μ z))) *
      radialStationaryProfile Ψ (-((j:ℝ)+(k:ℝ)+(n:ℝ))) s

theorem spherePairRadialCoefficientND_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (n : ℕ) (B : OrthonormalBasis ι ℝ V) (p q : Polynomial ℂ) (j k : ℕ)
    (hp : p.natDegree ≤ j) (hq : q.natDegree ≤ k) (C E : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (m : ℕ) : ∃ H : ℝ, 0 ≤ H ∧ ∀ (b c : SmoothFunctionND V) (A Λ Μ : ℝ),
      1 ≤ A → 0 < Λ → 0 < Μ → A^2 ≤ Λ → A^2 ≤ Μ →
      (∀ l ≤ 2*j, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ l b.1 w‖ ≤ C*A^l) →
      (∀ l ≤ 2*k, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ l c.1 w‖ ≤ E*A^l) →
      ∀ w z, ‖w‖=1 → ‖z‖=1 →
      ContDiff ℝ ∞ (spherePairRadialCoefficientND Ψ n B p q j k b c w z Λ Μ) ∧
      tsupport (spherePairRadialCoefficientND Ψ n B p q j k b c w z Λ Μ) ⊆ Icc (1/4:ℝ) 4 ∧
      ∀ l ≤ m, ∀ s, ‖iteratedDeriv l
        (spherePairRadialCoefficientND Ψ n B p q j k b c w z Λ Μ) s‖ ≤
        H*(Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2)) := by
  obtain ⟨D,hD,hDb⟩ := normalizedDifferentialND_bound B p j hp C hC
  obtain ⟨F,hF,hFb⟩ := normalizedDifferentialND_bound B q k hq E hE
  obtain ⟨P,hP,hPb⟩ := radialStationaryProfile_derivatives hΨ hs (-((j:ℝ)+(k:ℝ)+(n:ℝ))) m
  refine ⟨D*F*P,by positivity,?_⟩
  intro b c A Λ Μ hA hΛ hΜ hscale hscale' hb hc w z hw hz
  refine ⟨contDiff_const.mul (radialStationaryProfile_contDiff hΨ hs _),
    tsupport_mul_subset_right.trans (radialStationaryProfile_tsupport hs _),?_⟩
  intro l hl s
  change ‖iteratedDeriv l (fun t =>
    (((Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2):ℝ):ℂ) *
      (normalizedDifferentialND B p j b Λ w * star (normalizedDifferentialND B q k c Μ z))) *
        radialStationaryProfile Ψ (-((j:ℝ)+(k:ℝ)+(n:ℝ))) t) s‖ ≤ _
  rw [iteratedDeriv_const_mul_field]
  simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hΛ _),abs_of_pos (Real.rpow_pos_of_pos hΜ _)]
  calc
    _ ≤ (Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2))*(D*F)*P := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (mul_le_mul (hDb b A Λ hA hΛ hscale hb w hw)
          (hFb c A Μ hA hΜ hscale' hc z hz) (norm_nonneg _) hD) (by positivity))
        (hPb l hl s) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem spherePairRadialCoefficientND_kernel {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (n : ℕ) (B : OrthonormalBasis ι ℝ V) (p q : Polynomial ℂ) (j k : ℕ)
    (hp : p.natDegree ≤ j) (hq : q.natDegree ≤ k) (C E : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (b c : SmoothFunctionND V) (A R d₁ d₂ : ℝ),
      1 ≤ A → 0 < R → 0 < d₁ → 0 < d₂ → A^2 ≤ R*d₁ → A^2 ≤ R*d₂ →
      (∀ l ≤ 2*j, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ l b.1 w‖ ≤ C*A^l) →
      (∀ l ≤ 2*k, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ l c.1 w‖ ≤ E*A^l) →
      ∀ w z s₁ s₂, ‖w‖=1 → ‖z‖=1 →
      (s₁=1 ∨ s₁ = -1) → (s₂=1 ∨ s₂ = -1) →
      ‖radialPhaseIntegral
        (spherePairRadialCoefficientND Ψ n B p q j k b c w z (R*d₁) (R*d₂))
        (R*(s₁*d₁+s₂*d₂))‖ ≤
        H*((R*d₁)^(-(n:ℝ)/2)*(R*d₂)^(-(n:ℝ)/2))/(1+R*|d₁-d₂|)^2 := by
  obtain ⟨H,hH,hh⟩ := spherePairRadialCoefficientND_bound hΨ hs n B p q j k hp hq C E hC hE 2
  refine ⟨15*H,by positivity,?_⟩
  intro b c A R d₁ d₂ hA hR h1 h2 hscale hscale' hb hc w z s₁ s₂ hw hz hs1 hs2
  obtain ⟨ha,hsa,hba⟩ := hh b c A (R*d₁) (R*d₂) hA (mul_pos hR h1) (mul_pos hR h2)
    hscale hscale' hb hc w z hw hz
  have hb0 := hba 0 (by omega)
  simp only [iteratedDeriv_zero] at hb0
  have hx := angular_radial_kernel_bound ha hsa hH (by positivity) hR.le h1.le h2.le hs1 hs2
    hb0 (hba 2 le_rfl)
  exact hx.trans_eq (by ring)

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
open scoped ContDiff ComplexConjugate
abbrev PoleIndexND (J : ℕ) := Bool × Fin (J+1)

def poleSignND (s : Bool) : ℝ := if s then 1 else -1
lemma poleSignND_cases (s : Bool) : poleSignND s=1 ∨ poleSignND s = -1 := by
  cases s <;> simp [poleSignND]
lemma poleSignND_neg_cases (s : Bool) : -poleSignND s=1 ∨ -poleSignND s = -1 := by
  cases s <;> simp [poleSignND]

noncomputable def radialPoleSumND (n J : ℕ) (Λ : ℝ) (c : PoleIndexND J → ℂ) (u : ℝ) : ℂ :=
  ((Λ^(-(n:ℝ)/2):ℝ):ℂ) * ∑ i : PoleIndexND J,
    Complex.exp (Complex.I*((poleSignND i.1*Λ):ℂ)*(u:ℂ))*c i*
      (((u^(-(n:ℝ)/2-(i.2:ℕ)):ℝ):ℂ))

lemma radialPhaseIntegral_integrable {f : ℝ → ℂ} {a b : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a b) (ξ : ℝ) :
    Integrable (fun u : ℝ => Complex.exp (Complex.I*(ξ:ℂ)*(u:ℂ))*f u) := by
  have hcomp : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hs
  have hc : Continuous (fun u : ℝ => Complex.exp (Complex.I*(ξ:ℂ)*(u:ℂ))*f u) := by
    have := hf.continuous
    fun_prop
  exact hc.integrable_of_hasCompactSupport hcomp.mul_left

lemma pole_pair_integrand_identityND {Ψ : ℝ → ℝ}
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (n J : ℕ) (Λ Μ : ℝ) (c e : PoleIndexND J → ℂ) (u : ℝ) :
    (Ψ u:ℂ)*radialPoleSumND n J Λ c u*conj (radialPoleSumND n J Μ e u) =
      ∑ i : PoleIndexND J, ∑ j : PoleIndexND J,
        (((Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2):ℝ):ℂ)*(c i*conj (e j)))*
          (Complex.exp (Complex.I*((poleSignND i.1*Λ-poleSignND j.1*Μ):ℂ)*(u:ℂ))*
            radialStationaryProfile Ψ (-((n:ℝ)+(i.2:ℕ)+(j.2:ℕ))) u) := by
  by_cases hz : Ψ u=0
  · simp [hz,radialStationaryProfile]
  have hu : 0<u := lt_trans (by norm_num) (hs u hz).1
  simp only [radialPoleSumND,map_mul,map_sum,Complex.conj_ofReal,← Complex.exp_conj,
    Complex.conj_I,Finset.mul_sum,Finset.sum_mul,radialStationaryProfile]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hexp : Complex.exp (Complex.I*((poleSignND i.1*Λ):ℂ)*(u:ℂ))*
      Complex.exp (-Complex.I*((poleSignND j.1*Μ):ℂ)*(u:ℂ)) =
      Complex.exp (Complex.I*((poleSignND i.1*Λ-poleSignND j.1*Μ):ℂ)*(u:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hp : u^(-(n:ℝ)/2-(i.2:ℕ))*u^(-(n:ℝ)/2-(j.2:ℕ)) =
      u^(-((n:ℝ)+(i.2:ℕ)+(j.2:ℕ))) := by
    rw [← Real.rpow_add hu]
    congr 1
    ring
  push_cast at hexp ⊢
  calc
    _ = ((Λ^(-(n:ℝ)/2):ℝ):ℂ)*((Μ^(-(n:ℝ)/2):ℝ):ℂ)*(c i*conj (e j))*
        (Complex.exp (Complex.I*((poleSignND i.1*Λ):ℂ)*(u:ℂ))*
          Complex.exp (-Complex.I*((poleSignND j.1*Μ):ℂ)*(u:ℂ)))*
            (Ψ u:ℂ)*((u^(-(n:ℝ)/2-(i.2:ℕ))*u^(-(n:ℝ)/2-(j.2:ℕ)):ℝ):ℂ) := by
      push_cast
      ring
    _ = _ := by rw [hexp,hp]; ring

lemma pole_pair_integral_identityND {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (n J : ℕ) (Λ Μ : ℝ) (c e : PoleIndexND J → ℂ) :
    (∫ u, (Ψ u:ℂ)*radialPoleSumND n J Λ c u*conj (radialPoleSumND n J Μ e u)) =
      ∑ i : PoleIndexND J, ∑ j : PoleIndexND J,
        (((Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2):ℝ):ℂ)*(c i*conj (e j)))*
          radialPhaseIntegral (radialStationaryProfile Ψ (-((n:ℝ)+(i.2:ℕ)+(j.2:ℕ))))
            (poleSignND i.1*Λ-poleSignND j.1*Μ) := by
  simp_rw [pole_pair_integrand_identityND hs]
  have hi (i j : PoleIndexND J) :=
    (radialPhaseIntegral_integrable (radialStationaryProfile_contDiff hΨ hs (-((n:ℝ)+(i.2:ℕ)+(j.2:ℕ))))
      (radialStationaryProfile_tsupport hs (-((n:ℝ)+(i.2:ℕ)+(j.2:ℕ)))) (poleSignND i.1*Λ-poleSignND j.1*Μ)).const_mul
        ((((Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2):ℝ):ℂ)*(c i*conj (e j))))
  simp only [Complex.ofReal_sub,Complex.ofReal_mul] at hi ⊢
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [radialPhaseIntegral,Complex.ofReal_sub,Complex.ofReal_mul] using
    integral_const_mul (((Λ^(-(n:ℝ)/2):ℝ):ℂ)*((Μ^(-(n:ℝ)/2):ℝ):ℂ)*(c i*conj (e j)))
      (fun u : ℝ => Complex.exp (Complex.I*((poleSignND i.1*Λ-poleSignND j.1*Μ):ℂ)*(u:ℂ))*
        radialStationaryProfile Ψ (-((n:ℝ)+(i.2:ℕ)+(j.2:ℕ))) u)

theorem pole_pair_kernelND {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (n J : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (Λ Μ C E : ℝ) (c e : PoleIndexND J → ℂ),
      0<Λ → 0<Μ → 0≤C → 0≤E → (∀ i, ‖c i‖≤C) → (∀ i, ‖e i‖≤E) →
      ‖∫ u, (Ψ u:ℂ)*radialPoleSumND n J Λ c u*conj (radialPoleSumND n J Μ e u)‖ ≤
        H*C*E*(Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2))/(1+|Λ-Μ|)^2 := by
  have hex (i j : PoleIndexND J) := radialStationaryProfile_derivatives hΨ hs
    (-((n:ℝ)+(i.2:ℕ)+(j.2:ℕ))) 2
  choose H hH hD using hex
  refine ⟨∑ i : PoleIndexND J, ∑ j : PoleIndexND J, 15*H i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (by norm_num) (hH i j))),?_⟩
  intro Λ Μ C E c e hΛ hΜ hC hE hc he
  rw [pole_pair_integral_identityND hΨ hs]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun i _ => norm_sum_le _ _)).trans
  have hkernel (i j : PoleIndexND J) :
      ‖radialPhaseIntegral (radialStationaryProfile Ψ (-((n:ℝ)+(i.2:ℕ)+(j.2:ℕ))))
        (poleSignND i.1*Λ-poleSignND j.1*Μ)‖ ≤ 15*H i j/(1+|Λ-Μ|)^2 := by
    have h0 := hD i j 0 (by omega)
    simp only [iteratedDeriv_zero] at h0
    have h := angular_radial_kernel_bound (f := radialStationaryProfile Ψ (-((n:ℝ)+(i.2:ℕ)+(j.2:ℕ)))) (radialStationaryProfile_contDiff hΨ hs (-((n:ℝ)+(i.2:ℕ)+(j.2:ℕ))))
      (radialStationaryProfile_tsupport hs (-((n:ℝ)+(i.2:ℕ)+(j.2:ℕ)))) (hH i j) (show 0≤(1:ℝ) by norm_num)
      (show 0≤(1:ℝ) by norm_num) hΛ.le hΜ.le (poleSignND_cases i.1)
      (poleSignND_neg_cases j.1) (by simpa using h0) (by simpa using hD i j 2 le_rfl)
    simpa only [one_mul,mul_one,neg_mul,sub_eq_add_neg] using h
  calc
    _ ≤ ∑ i : PoleIndexND J, ∑ j : PoleIndexND J,
        (Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2))*(C*E)*(15*H i j/(1+|Λ-Μ|)^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hΛ _),abs_of_pos (Real.rpow_pos_of_pos hΜ _)]
      apply mul_le_mul _ (hkernel i j) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hc i) (he j) (norm_nonneg _) hC) (by positivity)
    _ = _ := by
      simp only [mul_div_assoc, ← Finset.sum_div, ← Finset.mul_sum]
      rw [mul_comm (Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2))]
      ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
