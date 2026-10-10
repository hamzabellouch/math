import OAI.MeasureTheory.Falconer.Incidence.CenteredPlanarIncidence
import OAI.MeasureTheory.Falconer.Incidence.CoarseSquashedPencils
import OAI.MeasureTheory.Falconer.Incidence.OriginalPencilEqualization

namespace OAI

/-! The complete original finite configuration at a chosen block depth.
The remaining numerical conditions concern only the scale and weak constants. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem original_block_incidence {κ s t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100)
    (hs : κ ≤ s) (hs1 : s ≤ 1-8*κ) (ht : s+8*κ ≤ t) (ht2 : t ≤ 2) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam ζ : ℝ, 0 < lam ∧ 0 < ζ ∧
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
    ∀ δ K : ℝ, 0 < δ → δ ≤ 1 → 1 ≤ K → 4*δ ≤ 1/(2:ℝ)^(m*B) →
      (let J : ℝ := (Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ);
       let F := (16*(1/(2:ℝ)^(m*B))/δ+1)^2;
       41472*K*J*F*2^t ≤ (2:ℝ)^((lam/4)*(m*B:ℕ)) ∧
       41472*K*J*F*4^s ≤ (2:ℝ)^(lam*(m*B:ℕ)) ∧
       81*F ≤ (2:ℝ)^(lam*(m*B:ℕ))) →
    ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P → FiniteSeparatedAt δ P →
      NormalizedFiniteBallBound δ t K P →
    ∀ V : Space 2 → Finset (Space 2),
      (∀ x ∈ P, (V x).Nonempty ∧ InBoundedLineChart (V x) ∧ FiniteSeparatedAt δ (V x) ∧
        NormalizedFiniteBallBound δ s K (V x) ∧ ∀ l ∈ V x, TubeIncident δ x l) →
      (2:ℝ)^((s+ζ)*(m*B:ℕ)) ≤
        (162*K*δ^s*(16*(1/(2:ℝ)^(m*B))/δ+1)^2)*((P.biUnion V).card:ℝ) := by
  obtain ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,hcentered⟩ := uniform_centered_planar_incidence hκ hκ1 hs hs1 ht
  refine ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,?_⟩
  intro m hm δ K hδ hδ1 hK hscale hcost P hP hPchart hPsep hPball V hV
  let N := m*B
  let J : ℝ := (Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ)
  let F := (16*(1/(2:ℝ)^N)/δ+1)^2
  have hJ : 1 ≤ J := by dsimp [J]; exact_mod_cast (show 1 ≤ Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1 by omega)
  have hF : 0 < F := by dsimp [F]; positivity
  obtain ⟨hcost1,hcost2,hcost3⟩ := hcost
  obtain ⟨k,P0,V0,hP0,_hP0P,hchart0,hsep0,hball0,hnumber,hV0,hunion0⟩ :=
    original_pencil_equalization hδ hδ1 hK P V hP hPchart hPsep hPball hV
  let K0 := 2*K*J
  have hK0 : 1 ≤ K0 := by
    have hh := one_le_mul_of_one_le_of_one_le hK hJ
    dsimp [K0]
    nlinarith only [hh]
  have hKJ : K*J ≤ K0 := by dsimp [K0]; nlinarith only [mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hJ)]
  have h2K : 2*K ≤ K0 := by
    dsimp [K0]
    exact le_mul_of_one_le_right (by linarith) hJ
  have mono {a b u : ℝ} {S : Finset (Space 2)} (hab : a ≤ b)
      (hb : NormalizedFiniteBallBound δ u a S) : NormalizedFiniteBallBound δ u b S := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg (hδ.le.trans hr) _)) (Nat.cast_nonneg _))
  have hv0 : ∀ x ∈ P0, (2:ℝ)^k ≤ ((V0 x).card:ℝ) ∧ ((V0 x).card:ℝ) ≤ (2:ℝ)^k ∧
      InBoundedLineChart (V0 x) ∧ FiniteSeparatedAt δ (V0 x) ∧
      NormalizedFiniteBallBound δ s K0 (V0 x) ∧ ∀ l ∈ V0 x, TubeIncident δ x l := by
    intro x hx
    have hh := hV0 x hx
    have hc : ((V0 x).card:ℝ) = (2:ℝ)^k := by exact_mod_cast hh.1
    exact ⟨hc.ge,hc.le,hh.2.1,hh.2.2.1,mono h2K hh.2.2.2.1,hh.2.2.2.2⟩
  obtain ⟨R,hR,hcarry,hRsep,hRball,U,hU,hunion⟩ := coarse_squashed_pencil_configuration hδ
    (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^N) (hκ.le.trans hs) (by linarith) (by linarith) ht2
    hK0 (by positivity : (0:ℝ) < (2:ℝ)^k) P0 V0 hP0 hchart0 hsep0 (mono hKJ hball0) hv0
  have hKfinal : 1 ≤ 20736*K0*F := by
    have hF1 : 1 ≤ F := by
      dsimp [F]
      have hh : 0 ≤ 16*(1/(2:ℝ)^N)/δ := by positivity
      nlinarith only [hh]
    have hh := one_le_mul_of_one_le_of_one_le hK0 hF1
    nlinarith only [hh]
  have hQside : (centeredUnitCube 2).side = 1 := rfl
  have hQcenter : (centeredUnitCube 2).center = 0 := by
    ext i
    change -(1/2:ℝ)+1/2 = 0
    ring
  have hsize : (2:ℝ)^k ≤ (2:ℝ)^(lam*(N:ℝ))*((2:ℝ)^k/(81*F)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 81*F)).2
    have hh := mul_le_mul_of_nonneg_left hcost3 (show 0 ≤ (2:ℝ)^k by positivity)
    nlinarith only [hh]
  have hgain := hcentered m hm (centeredUnitCube 2) hQside hQcenter (δ/4) (20736*K0*F)
    ((2:ℝ)^k/(81*F)) ((2:ℝ)^k) (by positivity) hKfinal (by positivity)
    (by nlinarith only [hscale])
    (by dsimp [K0]; convert hcost1 using 1; ring)
    (by dsimp [K0]; convert hcost2 using 1; ring) hsize R hR hcarry (by simpa only [mul_one_div,N] using hRsep) hRball U hU
  have hUorig : ((R.biUnion U).card:ℝ) ≤ ((P.biUnion V).card:ℝ) := hunion.trans hunion0
  have hga := (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^k/(81*F))).mp hgain
  have hmul := mul_le_mul_of_nonneg_right (hga.trans hUorig) (show 0 ≤ 81*F by positivity)
  have hcancel : (2:ℝ)^((s+ζ)*(N:ℝ))*((2:ℝ)^k/(81*F))*(81*F) =
      (2:ℝ)^((s+ζ)*(N:ℝ))*(2:ℝ)^k := by field_simp
  rw [hcancel] at hmul
  calc
    _ ≤ (2:ℝ)^((s+ζ)*(N:ℝ))*(2*K*δ^s*(2:ℝ)^k) :=
      le_mul_of_one_le_right (by positivity) hnumber
    _ = (2*K*δ^s)*((2:ℝ)^((s+ζ)*(N:ℝ))*(2:ℝ)^k) := by ring
    _ ≤ (2*K*δ^s)*(((P.biUnion V).card:ℝ)*(81*F)) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = _ := by dsimp [F]; ring

end Falconer

end OAI
