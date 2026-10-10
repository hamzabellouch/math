import OAI.MeasureTheory.Falconer.Radial.WeakRadialLosses
import OAI.MeasureTheory.Falconer.Radial.WeakRadialTotalCost
import OAI.MeasureTheory.Falconer.Radial.SingleClassRadialGain
import OAI.MeasureTheory.Falconer.Radial.RegularizationRadialGain
import OAI.MeasureTheory.Falconer.Radial.RadialRegularClasses
import OAI.MeasureTheory.Falconer.Radial.RadialProfileGap
import OAI.MeasureTheory.Falconer.Radial.RadialPinScaleBounds
import OAI.MeasureTheory.Falconer.Radial.RadialNearBallBounds

namespace OAI

/-! # The single-scale weak radial theorem in every dimension -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open Regularization
open scoped ENNReal
variable {n : ℕ}

theorem single_scale_weak_radial (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    {ζ ℓ : ℝ} (hζ : 0 < ζ) (hℓ : ℓ < ((n:ℝ)/(n+1))*(n:ℝ))
    (Q : DyadicCube (n+1)) (hQ : Q.side = 1) {M : ℝ} (hM : 1 ≤ M)
    (hbounded : ∀ x ∈ Q.carrier, ‖x‖ ≤ M) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ : Measure (Space (n+1))) [IsProbabilityMeasure μ], μ Q.carrierᶜ = 0 →
      (∀ x : Space (n+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^(n:ℝ))) →
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ a r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ {x | |inner ℝ w x-a| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
        (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ x w : Space (n+1), μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ ((2:ℝ)^N)⁻¹} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-ℓ)) := by
  obtain ⟨p⟩ := exists_weak_radial_losses hn hζ hℓ
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let C : ℝ := Real.sqrt (n+1:ℕ)+4*M
  let L : ℕ := Nat.ceil (C+1+((n+1:ℕ):ℝ)+1/2)
  have hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ) := Nat.le_ceil _
  have hC : Real.sqrt (n+1:ℕ)+2*(M+M) ≤ C := by dsimp [C]; linarith
  have hτ : 2*(((n+1:ℕ):ℝ)+1)*p.lam < p.τ := by
    convert p.regularization_gap using 1
    push_cast
    ring
  have hu : p.c*((n+1:ℕ):ℝ) < p.u := by
    simpa only [Nat.cast_add,Nat.cast_one] using p.incidence_gap
  have hv : p.c*((n+1:ℕ):ℝ) < p.η*ζ-p.ε := by
    simpa only [Nat.cast_add,Nat.cast_one] using p.slab_gap
  obtain ⟨Ns,hgain⟩ := single_class_radial_gain hLW hn Q hQ p.J p.J_pos L
    (e := p.e) (f := p.f) (τ := p.τ) (η := p.η) (lam := p.lam) (u := p.u)
    (v := p.η*ζ-p.ε) (c := p.c) (Cp := (2*M)^ζ) (Bs := M) (Bp := M) (C := C)
    p.η_pos.le (by positivity) hM0 hM0 hτ p.count_gap hu hv hL hC
    Q.carrier Q.measurable hbounded hbounded
  obtain ⟨H,Nr,hH,_,hcontrol,hclasses⟩ := radial_regular_classes (by omega : 2 ≤ n+1)
    Q hQ p.ε_pos.le p.ε_lt_lam
  have hcapgap : (p.J:ℝ)*(p.e+p.f)-((n:ℝ)/(n+1))*
      (((n+1:ℕ):ℝ)-1-((n:ℝ)+5)*p.lam-2*((n+1:ℕ):ℝ)/((p.J:ℝ)+2)) < -ℓ := by
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using p.cap_gap
  obtain ⟨Ng,hgap⟩ := eventually_radial_profile_gap (n+1) p.J hcapgap
  obtain ⟨Nb,hnear⟩ := eventually_radial_block_radius_le_one (A := 1) (by norm_num) (n+1) p.J
  have hD : (1:ℝ) ≤ 2*M := by linarith
  obtain ⟨Nl,hslabrange⟩ := radial_slab_scale_range hD p.η_pos (p.η_le.trans (by norm_num))
  let A : ℝ := (16*((n+1:ℕ):ℝ))^(n:ℝ)
  have ha : 0 < (n:ℝ)/((p.J:ℝ)+2)-p.ε := sub_pos.mpr p.near_gap
  obtain ⟨c,hc,Nc,hcost⟩ := weak_radial_total_cost p.J (4*H+2) (A := A)
    (by dsimp [A]; positivity) p.lam_pos ha p.c_pos p.f_pos
  refine ⟨p.ε,c,p.ε_pos,hc,Ns+Nr+Ng+Nb+Nl+Nc+H+(n+4)+1,?_⟩
  intro N hN μ _ hroot hball hslab
  have hNs : Ns ≤ N := by omega
  have hNr : Nr ≤ N := by omega
  have hNg : Ng ≤ N := by omega
  have hNb : Nb ≤ N := by omega
  have hNl : Nl ≤ N := by omega
  have hNc : Nc ≤ N := by omega
  have hNH : H ≤ N := by omega
  have hdN : (n+1)+3 ≤ N := by omega
  obtain ⟨hNpos,hB,hwidth,hlarge⟩ := hcontrol N hNr
  let R : ℝ := (2:ℝ)^N
  let K : ℝ≥0∞ := ENNReal.ofReal (A*R^(-((n:ℝ)/((p.J:ℝ)+2)-p.ε)))
  let t : ℝ≥0∞ := (p.J:ℝ≥0∞)*(K+ENNReal.ofReal (R^(-p.c)))+
    (p.J+1:ℝ≥0∞)*ENNReal.ofReal (R^(-p.f))
  have hball' : ∀ x : Space (n+1), ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (R^p.ε*r^(((n+1:ℕ):ℝ)-1)) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hball
  have hnear' : ∀ x : Space (n+1),
      μ (ball x (8*((n+1:ℕ):ℝ)/(2:ℝ)^(radialBlockSize N p.J))) ≤ K := by
    intro x
    have hh := radial_near_ball_bound (by omega : 2 ≤ n+1) μ N p.J hball'
      (by simpa only [mul_one] using hnear N hNb) x
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,A,K,R] using hh
  have hslab' : ∀ w : Space (n+1), ‖w‖ = 1 → ∀ a : ℝ,
      μ {x | |inner ℝ w x-a| ≤ (M+M)*R^(-p.η)} ≤
        ENNReal.ofReal ((2*M)^ζ*R^(-(p.η*ζ-p.ε))) := by
    have hh := radial_pin_slab_bound μ N (show 0 ≤ 2*M by positivity)
      (hslabrange N hNl).1 (hslabrange N hNl).2 hslab
    simpa only [two_mul,R] using hh
  have hreg := hclasses N hNr μ hroot hball'
  have hlocal : ∀ T ∈ regularizationIndex Q μ N (N/H) (ENNReal.ofReal (R^(-p.lam))),
      ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
        (μ.prod (normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T)) Gᶜ ≤ t ∧
        ∀ x w : Space (n+1), normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ R⁻¹} ≤ ENNReal.ofReal (R^(-ℓ)) := by
    intro T hT
    obtain ⟨_,p₀,hp₀,he,hprof⟩ := hreg.2.2 T hT
    have hm := hprof.envelope (1:ℝ) (by constructor <;> norm_num)
    have heq := sourceUnitProfile_at_depth Q μ hNpos (N/H) p₀ N
    rw [div_self (by exact_mod_cast hNpos.ne' : (N:ℝ) ≠ 0)] at heq
    rw [heq] at hm
    have hfinal : (n:ℝ)-((n:ℝ)+5)*p.lam ≤ sourceProfile Q μ N (N/H) p₀ N := by
      simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,mul_one] at hm
      convert hm using 1
      ring
    have hg := (hgap N hNg).2
    obtain ⟨G,hG,hcostG,hcapG⟩ := hgain N hNs μ μ hroot (N/H) hB hwidth hlarge p₀ hp₀
      (((n:ℝ)+5)*p.lam) ℓ hfinal
      (by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hg)
      K hnear' hslab'
    refine ⟨G,hG,?_,?_⟩
    · simpa only [sourceClass,he,t,R] using hcostG
    · simpa only [sourceClass,he,R] using hcapG
  obtain ⟨G,hG,hgc,hgcaps⟩ := regularization_radial_gain Q (by rw [hQ]; norm_num) μ μ
    hroot hH hNH hdN (threshold := ENNReal.ofReal (R^(-p.lam))) (by dsimp [R]; positivity)
    t (ENNReal.ofReal (R^(-ℓ))) R⁻¹ hlocal
  refine ⟨G,hG,hgc.trans ?_,hgcaps⟩
  simpa only [t,K,R,add_assoc] using hcost N hNc

end Falconer

end OAI
