import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Descent.Overlap

namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum
open UniqueFactorizationMonoid

namespace SevenEighths.InverseInitialOverlap

abbrev O := ActualEisensteinCubic.O

def residual (P j : Ideal O) : Ideal O := idealQuotient j P

def column (P j n : Ideal O) : Ideal O := idealQuotient j n * residual P j

def reconstruct (P j c : Ideal O) : Ideal O := j * idealQuotient (residual P j) c

def original (S : Finset (Ideal O)) (P j : Ideal O) : Finset (Ideal O) :=
  S.filter fun n => Squarefree n ∧ gcd n P = j

def columns (S : Finset (Ideal O)) (P j : Ideal O) : Finset (Ideal O) :=
  (original S P j).image (column P j)

theorem mem_original {S : Finset (Ideal O)} {P j n : Ideal O} :
    n ∈ original S P j ↔ n ∈ S ∧ Squarefree n ∧ gcd n P = j := by
  simp only [original, Finset.mem_filter]

theorem residual_mul {P j : Ideal O} (hj : j ∣ P) : j * residual P j = P :=
  idealQuotient_mul hj

theorem residual_squarefree {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) :
    Squarefree (residual P j) :=
  hP.squarefree_of_dvd (idealQuotient_dvd hj)

theorem quotient_mul_cancel {D H : Ideal O} (hD : D ≠ 0) :
    idealQuotient D (D * H) = H :=
  mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D H))

theorem column_properties {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hn : Squarefree n) (hg : gcd n P = j) :
    Squarefree (column P j n) ∧ IsCoprime (column P j n) j ∧
      residual P j ∣ column P j n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hHP : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have hHj := hHP.mono (dvd_refl _) hj
  have hHP0 := hHP.mono (dvd_refl _) (idealQuotient_dvd hj)
  have hJP0 : IsCoprime j (residual P j) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (j * residual P j) by rw [residual_mul hj]; exact hP)).1
  refine ⟨squarefree_mul_iff.mpr ⟨hHP0.isRelPrime,
    hn.squarefree_of_dvd (idealQuotient_dvd hjn), residual_squarefree hP hj⟩,
    hHj.mul_left hJP0.symm, dvd_mul_left _ _⟩

theorem reconstruct_column {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hg : gcd n P = j) : reconstruct P j (column P j n) = n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hP0 := (residual_squarefree hP hj).ne_zero
  unfold reconstruct column
  rw [mul_comm (idealQuotient j n), quotient_mul_cancel hP0, idealQuotient_mul hjn]

theorem reconstruct_properties {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hc : Squarefree c) (hcj : IsCoprime c j) (hPc : residual P j ∣ c) :
    Squarefree (reconstruct P j c) ∧ gcd (reconstruct P j c) P = j := by
  let H := idealQuotient (residual P j) c
  have hHc : H ∣ c := idealQuotient_dvd hPc
  have hHj : IsCoprime H j := hcj.mono hHc (dvd_refl _)
  have hHP0 : IsCoprime H (residual P j) :=
    (ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (residual P j * H) by rw [idealQuotient_mul hPc]; exact hc)).1).symm
  have hHP : IsCoprime H P := by
    rw [← residual_mul hj]
    exact hHj.mul_right hHP0
  exact ⟨squarefree_mul_iff.mpr ⟨hHj.symm.isRelPrime,
    hP.squarefree_of_dvd hj, hc.squarefree_of_dvd hHc⟩,
    gcd_mul_of_coprime_divisor j H P hj hHP⟩

theorem column_reconstruct {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) : column P j (reconstruct P j c) = c := by
  have hj0 : j ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero hj
  unfold column reconstruct
  rw [quotient_mul_cancel hj0, mul_comm, idealQuotient_mul hPc]

theorem mem_columns {S : Finset (Ideal O)} {P j c : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    c ∈ columns S P j ↔ Squarefree c ∧ IsCoprime c j ∧
      residual P j ∣ c ∧ reconstruct P j c ∈ S := by
  constructor
  · intro hc
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hnS, hn, hg⟩ := mem_original.mp hn
    obtain ⟨hcs, hcj, hPc⟩ := column_properties hP hj hn hg
    exact ⟨hcs, hcj, hPc, by rwa [reconstruct_column hP hj hg]⟩
  · rintro ⟨hc, hcj, hPc, hnS⟩
    obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hc hcj hPc
    exact Finset.mem_image.mpr ⟨reconstruct P j c,
      mem_original.mpr ⟨hnS, hn, hg⟩, column_reconstruct hP hj hPc⟩

theorem column_injOn (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    Set.InjOn (column P j) (original S P j) := by
  intro n hn m hm he
  have hn' := reconstruct_column hP hj (mem_original.mp hn).2.2
  have hm' := reconstruct_column hP hj (mem_original.mp hm).2.2
  rw [← hn', ← hm', he]

def overlapEquiv (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) : original S P j ≃ columns S P j where
  toFun n := ⟨column P j n, Finset.mem_image.mpr ⟨n, n.property, rfl⟩⟩
  invFun c := ⟨reconstruct P j c, by
    obtain ⟨hc, hcj, hPc, hnS⟩ := (mem_columns hP hj).mp c.property
    exact mem_original.mpr ⟨hnS, reconstruct_properties hP hj hc hcj hPc⟩⟩
  left_inv n := Subtype.ext (reconstruct_column hP hj (mem_original.mp n.property).2.2)
  right_inv c := Subtype.ext (column_reconstruct hP hj
    ((mem_columns hP hj).mp c.property).2.2.1)

theorem reconstruct_mul_residual {P j c : Ideal O} (hPc : residual P j ∣ c) :
    reconstruct P j c * residual P j = j * c := by
  unfold reconstruct
  rw [mul_assoc, mul_comm (idealQuotient _ _), idealQuotient_mul hPc]

theorem norm_reconstruct {P j c : Ideal O} (hPc : residual P j ∣ c) :
    Ideal.absNorm (reconstruct P j c) * Ideal.absNorm (residual P j) =
      Ideal.absNorm j * Ideal.absNorm c := by
  simpa only [map_mul] using congrArg Ideal.absNorm (reconstruct_mul_residual hPc)

theorem cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) (X : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / X =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c /
        ((Ideal.absNorm (residual P j) : ℝ) * X) := by
  have h0 : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hn : (Ideal.absNorm (reconstruct P j c) : ℝ) =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c / Ideal.absNorm (residual P j) := by
    apply (eq_div_iff h0).mpr
    exact_mod_cast norm_reconstruct hPc
  rw [hn, div_div]

theorem columns_filter (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (mask : Ideal O → Prop) [DecidablePred mask] :
    columns (S.filter mask) P j =
      (columns S P j).filter fun c => mask (reconstruct P j c) := by
  ext c
  simp only [mem_columns hP hj, Finset.mem_filter]
  tauto

theorem sum_reconstruct (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (F : Ideal O → ℂ) :
    (∑ n ∈ original S P j, F n) =
      ∑ c ∈ columns S P j, F (reconstruct P j c) := by
  rw [columns, Finset.sum_image (column_injOn S hP hj)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [reconstruct_column hP hj (mem_original.mp hn).2.2]

theorem coefficient_identity (ψ : Ideal O →* ℂ) {P j n : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (hn : Squarefree n) (hg : gcd n P = j) :
    (moebius n : ℂ) * ψ n * ψ P =
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2 *
        ((moebius (column P j n) : ℂ) * ψ (column P j n)) := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hH : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have h := InverseMoment.moebius_character_overlap ψ
    (hH.mono (dvd_refl _) hj).symm.isRelPrime
    (hH.mono (dvd_refl _) (idealQuotient_dvd hj)).isRelPrime
    (residual_squarefree hP hj)
  rw [idealQuotient_mul hjn, idealQuotient_mul hj] at h
  change (moebius n : ℂ) * ψ n * ψ P = _
  rw [h]
  unfold column residual
  ring

theorem polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    (∑ n ∈ original S P j,
      (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / X)) =
    ((moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * X)) := by
  rw [sum_reconstruct S hP hj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨hcs, hcj, hPc, _⟩ := (mem_columns hP hj).mp hc
  obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hcs hcj hPc
  rw [coefficient_identity ψ hP hj hn hg, column_reconstruct hP hj hPc,
    cutoff_argument hP hj hPc]
  ring

theorem sum_original_partition (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (F : Ideal O → ℂ) :
    (∑ n ∈ S.filter Squarefree, F n) =
      ∑ j ∈ idealDivisors P, ∑ n ∈ original S P j, F n := by
  have hmap : ∀ n ∈ S.filter Squarefree, gcd n P ∈ idealDivisors P := by
    intro n _
    exact (mem_idealDivisors hP.ne_zero).mpr (GCDMonoid.gcd_dvd_right _ _)
  have h := Finset.sum_fiberwise_of_maps_to hmap F
  simpa only [original, Finset.filter_filter] using h.symm

theorem polynomial_all_overlaps (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    (∑ n ∈ S.filter Squarefree,
      (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / X)) =
    ∑ j ∈ idealDivisors P,
      ((moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
            ((Ideal.absNorm (residual P j) : ℝ) * X)) := by
  rw [sum_original_partition S hP]
  apply Finset.sum_congr rfl
  intro j hj
  exact polynomial_fixed_overlap S hP ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W X

theorem scaled_cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / Z ^ r =
      (((Ideal.absNorm j : ℝ) / Z ^ G) *
        ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
        ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G)) := by
  have hnorm : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hscale : Z ^ G * Z ^ (r + z - 2 * G) = Z ^ r * Z ^ (z - G) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  rw [cutoff_argument hP hj hPc]
  rw [div_mul_div_comm, div_div_eq_mul_div]
  field_simp [hnorm, (Real.rpow_pos_of_pos hZ r).ne',
    (Real.rpow_pos_of_pos hZ G).ne',
    (Real.rpow_pos_of_pos hZ (r + z - 2 * G)).ne',
    (Real.rpow_pos_of_pos hZ (z - G)).ne']
  linear_combination ((Ideal.absNorm j : ℝ) * Ideal.absNorm c) * hscale

theorem normalization_split {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    Z ^ (-(r + z) / 2) = Z ^ (-G) * Z ^ (-(r + z - 2 * G) / 2) := by
  rw [← Real.rpow_add hZ]
  congr 1
  ring

theorem normalized_polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ original S P j,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
      (Z ^ (-G) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G) / 2) : ℝ) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
  rw [polynomial_fixed_overlap S hP hj ψ a W, normalization_split hZ r z G,
    Complex.ofReal_mul]
  have hs : (∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * Z ^ r))) =
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hPc := ((mem_columns hP hj).mp hc).2.2.1
    rw [← cutoff_argument hP hj hPc, scaled_cutoff_argument hP hj hPc hZ]
  rw [hs]
  ring

theorem normalized_polynomial_all_overlaps (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S.filter Squarefree,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  rw [sum_original_partition S hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact normalized_polynomial_fixed_overlap S hP
    ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W hZ r z (G j)

theorem sum_moebius_filter (S : Finset (Ideal O)) (F : Ideal O → ℂ) :
    (∑ n ∈ S, (moebius n : ℂ) * F n) =
      ∑ n ∈ S.filter Squarefree, (moebius n : ℂ) * F n := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnf
  have hns : ¬ Squarefree n := fun h => hnf (Finset.mem_filter.mpr ⟨hn, h⟩)
  simp only [moebius_of_not_squarefree hns, Int.cast_zero, zero_mul]

theorem original_normalized_polynomial (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  have hf := sum_moebius_filter S (fun n =>
    ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r))
  simp only [← mul_assoc] at hf
  rw [hf]
  exact normalized_polynomial_all_overlaps S hP ψ a W hZ r z G

theorem overlap_coefficient_norm_le {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (ψ : Ideal O →* ℂ) (hψ : ‖ψ j‖ ≤ 1) :
    ‖(moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2‖ ≤ 1 := by
  have hjSF := hP.squarefree_of_dvd hj
  have hresSF := residual_squarefree hP hj
  simpa [norm_mul, hjSF.moebius_eq, hresSF.moebius_eq] using
    InverseMoment.overlap_scalar_norm_le hψ

end SevenEighths.InverseInitialOverlap

end

end OAI
