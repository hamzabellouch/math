import OAI.MeasureTheory.Falconer.Graphs.OuterRootGraphBound
import OAI.MeasureTheory.Falconer.Estimates.OuterEntryProfile

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

theorem separated_unit_roots_distance (Q : Fin 2 → DyadicSquare)
    (hQ : ∀ l, (Q l).side = 1)
    (hlo : 100 ≤ dist (Q 0).center (Q 1).center)
    (hhi : dist (Q 0).center (Q 1).center ≤ 2000)
    (x y : Plane) (hx : x ∈ (Q 0).carrier) (hy : y ∈ (Q 1).carrier) :
    90 ≤ dist x y ∧ dist x y ≤ 2010 := by
  have hx' := (Q 0).dist_center_le_three_quarters (by rw [hQ 0]; norm_num) hx
  have hy' := (Q 1).dist_center_le_three_quarters (by rw [hQ 1]; norm_num) hy
  rw [hQ 0] at hx'
  rw [hQ 1] at hy'
  have hl := dist_triangle4 (Q 0).center x y (Q 1).center
  have hu := dist_triangle4 x (Q 0).center (Q 1).center y
  rw [dist_comm (Q 0).center x] at hl
  rw [dist_comm (Q 1).center y] at hu
  constructor <;> linarith

theorem uniform_normalized_outer_shell {δ β lam sig kap eta : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10)
    (hlam : 0 ≤ lam) (hlamδ : lam < δ/1000) (hsig : 0 < sig)
    (hkap : 0 < kap) (hkapβ : 1000000*kap < β) (hgap : sig < kap/1000)
    (hloss : 4000*(lam+sig) ≤ 1) (heta : 0 < eta)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ),
      (∀ l, (Q l).side = 1) → (∀ l, ρ l (Q l).carrierᶜ = 0) →
      100 ≤ dist (Q 0).center (Q 1).center → dist (Q 0).center (Q 1).center ≤ 2000 →
      ∀ B : ℕ, (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
      let c := outerEntry (mass 0) (mass 1) N β
      let d := RootShellData.ofOuter (Q 0) (Q 1) (ρ 0) (ρ 1) (mass 0) (mass 1)
        N lam lam sig kap c (Q 0) (Q 1)
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤
        ((2:ℝ)^N)^(-β+500*kap+10^6*(lam+sig)/kap+4000*(lam+sig)+5*lam+eta) := by
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hβsmall : β < 1 := by linarith
  have hkap1 : kap ≤ 1 := by linarith
  obtain ⟨n,N₁,h₁⟩ := RootShellData.uniform_outer_equation21 (δ := 90) (L := 2010) (T := 10)
    hsig (source_root_sigma_small hδ1 hβ hkapβ hgap) hkap (by norm_num) (by norm_num)
    (by positivity : 0 < eta/8)
  obtain ⟨N₂,hN₂,h₂⟩ := uniform_outer_root_graph_bound hlam hsig hkap hkap1 hgap hloss
    (by positivity : 0 < eta/8) (by norm_num : (0:ℝ) ≤ 10) n hΨ hpos hs hone
  obtain ⟨N₃,hN₃⟩ := exists_nat_ge (max (8/eta) (2/β))
  obtain ⟨N₄,h₄⟩ := fixed_constant_absorbed (half_pos heta) (3:ℝ)
  refine ⟨max 400 (max N₁ (max N₂ (max N₃ N₄))),by omega,?_⟩
  intro N hN Q ρ mass hQ hcarry hlo hhi B hprof
  have hN400 : 400 ≤ N := by omega
  have hN₁' : N₁ ≤ N := by omega
  have hN₂' : N₂ ≤ N := by omega
  have hN₃' : N₃ ≤ N := by omega
  have hN₄' : N₄ ≤ N := by omega
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hentry : 2 ≤ β*(N:ℝ) := by
    have he := (le_max_right (8/eta) (2/β)).trans (hN₃.trans (Nat.cast_le.mpr hN₃'))
    have he' := (div_le_iff₀ hβpos).mp he
    linarith
  have hsmallN : 2/(N:ℝ) ≤ eta/4 := by
    have he := (le_max_left (8/eta) (2/β)).trans (hN₃.trans (Nat.cast_le.mpr hN₃'))
    have he' := (div_le_iff₀ heta).mp he
    apply (div_le_iff₀ hNpos).mpr
    linarith
  obtain ⟨hcN,hclo,hchi,hkc,hc2,hw,htail,hgain⟩ := outer_entry_profile_bounds
    hδ hδ1 hβ hlam hlamδ hkap hkapβ N hN400 hentry Q ρ mass B hprof
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hprof l).probability
  have hQpos (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  have hcarry' (l : Fin 2) : ∀ᵐ x ∂ρ l, x ∈ (Q l).carrier := ae_iff.mpr (hcarry l)
  obtain ⟨W,hW,hWbound⟩ := continuous_supported_bump_bound hΨ.continuous hs
  let c := outerEntry (mass 0) (mass 1) N β
  let A := fun l (t : ℕ) => mass l t-(t:ℝ)/N
  let d := RootShellData.ofOuter (Q 0) (Q 1) (ρ 0) (ρ 1) (mass 0) (mass 1)
    N lam lam sig kap c (Q 0) (Q 1)
  have hconv := h₁ N hN₁' (Q 0) (Q 1) (hQpos 0) (hQpos 1) (ρ 0) (ρ 1)
    (mass 0) (mass 1) lam lam c hc2 (Q 0) (Q 1) (hQpos 0) (hQpos 1)
    (hcarry' 0) (hcarry' 1) (fun x hx y hy => separated_unit_roots_distance Q hQ hlo hhi x y hx hy)
    1 (by rw [hQ 0]) (by rw [hQ 1]) (by simpa using hlo)
    Ψ hΨ.continuous.measurable hpos hs W hW (fun x => (le_abs_self _).trans (hWbound x)) hone
  have hgraph := (h₂ N hN₂' Q ρ mass hQ hcarry hlo hhi B δ hprof c hw hkc hc2).2
  let loss := 500*kap+10^6*(lam+sig)/kap+4000*(lam+sig)+5*lam
  let g := min (height (A 0) 0 c) (height (A 1) 0 c)-
    (potential (A 0) c N (10*sourcePolicyBlock N kap)+
     potential (A 1) c N (10*sourcePolicyBlock N kap))/2+
    500*kap+10^6*(lam+sig)/kap+4000*(lam+sig)+eta/8
  have hloss0 : 0 ≤ loss := by dsimp only [loss]; positivity
  have hexp : eta/8+g ≤ -β+loss+eta/2 := by dsimp only [g,loss]; linarith
  have hmain : ((2:ℝ)^N)^(eta/8)*((2:ℝ)^N)^g ≤ ((2:ℝ)^N)^(-β+loss+eta/2) := by
    rw [← Real.rpow_add (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hexp
  have herr₁ : ((2:ℝ)^N)^(eta/8)*((2:ℝ)^N)^(-10:ℝ) ≤ ((2:ℝ)^N)^(-β+loss+eta/2) := by
    rw [← Real.rpow_add (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
  have herr₂ : ((2:ℝ)^N)^(-10:ℝ) ≤ ((2:ℝ)^N)^(-β+loss+eta/2) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
  change (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤ _
  calc
    _ ≤ ((2:ℝ)^N)^(eta/8)*d.inverseShellSupremum n N Ψ+((2:ℝ)^N)^(-10:ℝ) := hconv
    _ ≤ ((2:ℝ)^N)^(eta/8)*(((2:ℝ)^N)^g+((2:ℝ)^N)^(-10:ℝ))+((2:ℝ)^N)^(-10:ℝ) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hgraph (by positivity)) le_rfl
    _ ≤ 3*((2:ℝ)^N)^(-β+loss+eta/2) := by rw [mul_add]; linarith
    _ ≤ ((2:ℝ)^N)^(eta/2)*((2:ℝ)^N)^(-β+loss+eta/2) :=
      mul_le_mul_of_nonneg_right (h₄ N hN₄') (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; dsimp only [loss]; ring

theorem uniform_normalized_equation27 {δ β lam sig kap : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10)
    (hlam : 0 < lam) (hlamδ : lam < δ/1000) (hsig : 0 < sig)
    (hkap : 0 < kap) (hkapβ : 1000000*kap < β) (hgap : sig < kap/1000)
    (hratio : 10000000*(lam+sig)/kap < β/100)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ),
      (∀ l, (Q l).side = 1) → (∀ l, ρ l (Q l).carrierᶜ = 0) →
      100 ≤ dist (Q 0).center (Q 1).center → dist (Q 0).center (Q 1).center ≤ 2000 →
      ∀ B : ℕ, (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
      let c := outerEntry (mass 0) (mass 1) N β
      let d := RootShellData.ofOuter (Q 0) (Q 1) (ρ 0) (ρ 1) (mass 0) (mass 1)
        N lam lam sig kap c (Q 0) (Q 1)
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤
        ((2:ℝ)^N)^(-β/2) := by
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hkap1 : kap < 1 := by linarith
  have hloss := parameter_loss_bound hβpos hkap hkap1 hlam.le hsig.le hkapβ hratio
  have hh := source_parameter_recursion_hierarchy hδ1 hlam hsig hkap
    (by norm_num [hβ] at hkapβ ⊢; exact hkapβ) hgap (by norm_num [hβ] at hratio ⊢; exact hratio)
  let loss := 500*kap+10^6*(lam+sig)/kap+4000*(lam+sig)+5*lam
  have he : 0 < β/2-loss := by
    apply sub_pos.mpr
    dsimp only [loss]
    norm_num
    exact hloss
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_normalized_outer_shell hδ hδ1 hβ hlam.le hlamδ hsig
    hkap hkapβ hgap hh.2.2.2.2.2.le he hΨ hpos hs hone
  refine ⟨N₀,hN₀,?_⟩
  intro N hN Q ρ mass hQ hcarry hlo hhi B hprof
  have hb := h₀ N hN Q ρ mass hQ hcarry hlo hhi B hprof
  apply hb.trans_eq
  congr 1
  dsimp only [loss]
  ring

end PlanarFalconer

end OAI
