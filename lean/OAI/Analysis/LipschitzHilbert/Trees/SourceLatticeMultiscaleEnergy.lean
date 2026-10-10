import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeScaleEnergy
import OAI.Analysis.LipschitzHilbert.Estimates.PlanarColoredVectorEnergy

namespace OAI

/-! The ordinary multiscale energy estimate for the original physical
lattice packets. Residue coloring has a fixed cost determined only by
the annular constants, not the number of lengths or vector bins. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert

private theorem planarSchwartzSlice_sum_smul {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (y t : ℝ) :
    planarSchwartzSlice (∑ i, a i • f i) y t =
      ∑ i, a i • planarSchwartzSlice (f i) y t := by
  ext x
  simp only [planarSchwartzSlice_apply,sum_apply,smul_apply]

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

/-- The cutoff at one retained coefficient needs only that packet's
selector separation; all other coefficients may vanish. -/
theorem raw_fourier_cutoffs_at (P : SourceLatticePacket N κ ι)
    (t w cStar cEta CEta cb Cb : ℝ) (hw : 0 < w)
    (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (j : Fin N) (u : ι j) (k : κ)
    (hspectrum : ∀ ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η) ≠ 0 →
      |ξ+(t+P.rowSlope j)*η| ≤ cStar/P.length j ∧ cEta ≤ w*η ∧ w*η ≤ CEta)
    (hselector : cb*w/P.length j ≤ |P.rowSlope j| ∧ |P.rowSlope j| ≤ Cb*w/P.length j)
    (i : Fin 3) (y : ℝ) :
    (∀ ξ, |ξ| < (((cEta*cb-cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val →
      𝓕 (P.raw i j u k y) ξ = 0) ∧
    (∀ ξ, (((CEta*Cb+cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val < |ξ| →
      𝓕 (P.raw i j u k y) ξ = 0) := by
  have hsel : cb*w/P.length j ≤ |t-(t+P.rowSlope j)| ∧
      |t-(t+P.rowSlope j)| ≤ Cb*w/P.length j := by
    have heq : t-(t+P.rowSlope j) = -P.rowSlope j := by ring
    simpa only [heq,abs_neg] using hselector
  have h := sourcePacket_jet_fourier_cutoffs (P.physicalPacket t j u k)
    y t (t+P.rowSlope j) (P.length j) w cStar cEta CEta cb Cb
    (P.length_pos j) hw hcEta hcb hCb hspectrum hsel (P.frequency k) P.scale i
  have hraw : P.raw i j u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j u k) (P.frequency k) P.scale i) y t :=
    P.raw_eq_physical_slice i j u k y t
  have heq (A : ℝ) : A/(2*Real.pi*P.length j) =
      ((A/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val := by
    rw [SourceLatticePacket.length,packet_annulus_dyadic_scale A P.topLength j.val P.topLength_pos.ne']
    ring
  rw [← hraw,heq,heq] at h
  exact h

/-- The qualitative L² assertion accompanies the numerical estimate. -/
theorem physicalMultiscaleSynthesis_memLp (P : SourceLatticePacket N κ ι)
    (t : ℝ) (c : ∀ j, ι j → EuclideanSpace ℂ κ) :
    MemLp (fun z => ∑ j, planarFixedSynthesis (c j) (P.physicalPacket t j) z)
      2 (volume.prod volume) :=
  memLp_finsetSum _ (fun j _ => planarFixedSynthesis_memLp (c j) (P.physicalPacket t j))

end SourceLatticePacket

/-- The constant is fixed before every finite index type and packet
family. Empty scales require no selector assumption. -/
theorem exists_physical_lattice_multiscale_energy
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (t w : ℝ), 0 < w →
    ∀ c : ∀ j, ι j → EuclideanSpace ℂ κ,
      (∀ j u k ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η) ≠ 0 →
        |ξ+(t+P.rowSlope j)*η| ≤ cStar/P.length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta) →
      (∀ j (u : ι j) k, c j u k ≠ 0 → cb*w/P.length j ≤ |P.rowSlope j| ∧
        |P.rowSlope j| ≤ Cb*w/P.length j) →
      (∫ z, ‖∑ j, planarFixedSynthesis (c j) (P.physicalPacket t j) z‖^2
        ∂volume.prod volume) ≤
        C*P.profileBound^2*∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
  let lower := (cEta*cb-cStar)/(2*Real.pi)
  let upper := (CEta*Cb+cStar)/(2*Real.pi)
  have hlower : 0 < lower := div_pos (sub_pos.mpr hgap) (by positivity)
  obtain ⟨q,hq,hsep⟩ := exists_dyadic_annular_separation (upper := upper) hlower
  let C := (q:ℝ)*((4*Real.pi)^2*Real.pi^2)
  have hqreal : 0 < (q:ℝ) := by exact_mod_cast hq
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro N κ ι _ _ P t w hw c hspectrum hselector
  let G := fun j k => (∑ u, c j u k • P.physicalPacket t j u k : SchwartzMap (ℝ×ℝ) ℂ)
  have hG (j : Fin N) (z : ℝ×ℝ) :
      (WithLp.toLp 2 (fun k => G j k z) : EuclideanSpace ℂ κ) =
        planarFixedSynthesis (c j) (P.physicalPacket t j) z := by
    ext k
    simp only [G,planarFixedSynthesis,WithLp.ofLp_toLp,sum_apply,smul_apply,smul_eq_mul]
  have hraw (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
      planarSchwartzSlice (P.physicalPacket t j u k) y t = P.raw 0 j u k y := by
    have h : P.raw 0 j u k y = planarSchwartzSlice
        (planarCovariantJet (P.physicalPacket t j u k) (P.frequency k) P.scale 0) y t :=
      P.raw_eq_physical_slice 0 j u k y t
    simpa only [planarCovariantJet,ite_true] using h.symm
  have hout (j : Fin N) (k : κ) (y ξ : ℝ)
      (hξ : |ξ| < (lower/P.topLength)*(2:ℝ)^j.val ∨
        (upper/P.topLength)*(2:ℝ)^j.val < |ξ|) :
      𝓕 (planarSchwartzSlice (G j k) y t) ξ = 0 := by
    have hz (u : ι j) : c j u k * 𝓕 (P.raw 0 j u k y) ξ = 0 := by
      by_cases hc : c j u k = 0
      · simp only [hc,zero_mul]
      have h := P.raw_fourier_cutoffs_at t w cStar cEta CEta cb Cb hw hcEta hcb hCb
        j u k (hspectrum j u k) (hselector j u k hc) 0 y
      have hfzero : 𝓕 (P.raw 0 j u k y) ξ = 0 := by
        rcases hξ with hl | hu
        · exact h.1 ξ hl
        · exact h.2 ξ hu
      simp only [hfzero,mul_zero]
    change (SchwartzMap.fourierTransformCLM ℂ (planarSchwartzSlice (G j k) y t)) ξ = 0
    rw [show planarSchwartzSlice (G j k) y t =
      ∑ u, c j u k • P.raw 0 j u k y by
        dsimp only [G]
        rw [planarSchwartzSlice_sum_smul]
        simp only [hraw]]
    rw [map_sum]
    simp only [map_smul,sum_apply,smul_apply,smul_eq_mul]
    change (∑ u, c j u k * 𝓕 (P.raw 0 j u k y) ξ) = 0
    simp only [hz,Finset.sum_const_zero]
  have hsep' (i j : Fin N) (hij : i < j) (hmod : i.val % q = j.val % q) :
      (upper/P.topLength)*(2:ℝ)^i.val < (lower/P.topLength)*(2:ℝ)^j.val := by
    have h := div_lt_div_of_pos_right (hsep i.val j.val hij hmod) P.topLength_pos
    convert h using 1 <;> ring
  have henergy := planar_colored_vector_energy G (fun j : Fin N => ⟨j.val % q,Nat.mod_lt _ hq⟩) t
    (by
      intro k y ξ i j hij hcolor
      have hmod : i.val % q = j.val % q := congrArg Fin.val hcolor
      rcases lt_or_gt_of_ne hij with hij | hji
      · by_cases hj : |ξ| < (lower/P.topLength)*(2:ℝ)^j.val
        · exact Or.inr (hout j k y ξ (Or.inl hj))
        · exact Or.inl (hout i k y ξ (Or.inr ((hsep' i j hij hmod).trans_le (le_of_not_gt hj))))
      · by_cases hi : |ξ| < (lower/P.topLength)*(2:ℝ)^i.val
        · exact Or.inl (hout i k y ξ (Or.inl hi))
        · exact Or.inr (hout j k y ξ (Or.inr ((hsep' j i hji hmod.symm).trans_le (le_of_not_gt hi)))))
  simp only [hG] at henergy
  apply henergy.trans
  calc
    _ ≤ (q:ℝ)*∑ j, ((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
          ∑ u, ‖c j u‖^2*P.length j*P.width :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun j _ => P.physicalPacket_scale_energy t j (c j))) hqreal.le
    _ = _ := by rw [← Finset.mul_sum]; dsimp [C]; ring

end LipschitzHilbert

end

end OAI
