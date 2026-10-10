import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralCornerDensity
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeDihedral

namespace OAI

/-! The centered dihedral corner is generated in L² by the positive
compressed rotation powers. Apply the bounded centered corner map to the
ordinary rotation/reflection word span; no bounded approximation theorem
or corner-freeness hypothesis is needed. -/

noncomputable section
namespace KadisonSimilarity

section Algebra
variable {P : Type*} [Ring P] [Algebra ℂ P]

/-- Both sides of the half projection absorb its reflection. -/
theorem halfProjection_absorbs_reflection (d : Pˣ) (hd : d * d = 1) :
    dihedralHalfProjection d * (d : P) = dihedralHalfProjection d ∧
      (d : P) * dihedralHalfProjection d = dihedralHalfProjection d := by
  have hd' : (d : P) * (d : P) = 1 := by rw [← Units.val_mul, hd, Units.val_one]
  constructor
  · simp only [dihedralHalfProjection, smul_mul_assoc, add_mul, one_mul, hd']
    congr 1
    abel
  · simp only [dihedralHalfProjection, mul_smul_comm, mul_add, mul_one, hd']
    congr 1
    abel

/-- Reflection conjugation makes opposite rotation powers equal after
compression to the half projection. -/
theorem halfProjection_compressed_neg (d w : Pˣ) (hd : d * d = 1)
    (hconj : d * w = w⁻¹ * d) (l : ℤ) :
    dihedralHalfProjection d * (↑(w ^ (-l)) : P) * dihedralHalfProjection d =
      dihedralHalfProjection d * (↑(w ^ l) : P) * dihedralHalfProjection d := by
  obtain ⟨hpd, hdp⟩ := halfProjection_absorbs_reflection d hd
  have hm := (show SemiconjBy d w w⁻¹ from hconj).zpow_right l
  have hm' : (d : P) * (↑(w ^ l) : P) = (↑(w ^ (-l)) : P) * (d : P) := by
    have h := congrArg (fun a : Pˣ => (a : P)) hm.eq
    simpa only [Units.val_mul, inv_zpow, zpow_neg] using h
  calc
    _ = dihedralHalfProjection d * (↑(w ^ (-l)) : P) *
        ((d : P) * dihedralHalfProjection d) := by rw [hdp]
    _ = dihedralHalfProjection d * ((↑(w ^ (-l)) : P) * (d : P)) *
        dihedralHalfProjection d := by simp only [mul_assoc]
    _ = dihedralHalfProjection d * ((d : P) * (↑(w ^ l) : P)) *
        dihedralHalfProjection d := by rw [← hm']
    _ = _ := by rw [← mul_assoc (dihedralHalfProjection d) (d : P), hpd]

/-- Every compressed nonzero integer power is a positive compressed power. -/
theorem halfProjection_compressed_natAbs (d w : Pˣ) (hd : d * d = 1)
    (hconj : d * w = w⁻¹ * d) (l : ℤ) :
    dihedralHalfProjection d * (↑(w ^ l) : P) * dihedralHalfProjection d =
      dihedralHalfProjection d * (w : P) ^ l.natAbs * dihedralHalfProjection d := by
  cases l with
  | ofNat n => rfl
  | negSucc n =>
    have h := halfProjection_compressed_neg d w hd hconj ((n + 1 : ℕ) : ℤ)
    rw [zpow_natCast, Units.val_pow_eq_pow_val] at h
    have heq : -((n + 1 : ℕ) : ℤ) = Int.negSucc n := by omega
    rw [heq] at h
    exact h

/-- Reflection-coset words have the same corner compression as rotations. -/
theorem halfProjection_compressed_coset (d w : Pˣ) (hd : d * d = 1) (l : ℤ) :
    dihedralHalfProjection d * ((↑(w ^ l) : P) * (d : P)) * dihedralHalfProjection d =
      dihedralHalfProjection d * (↑(w ^ l) : P) * dihedralHalfProjection d := by
  rw [mul_assoc, mul_assoc, (halfProjection_absorbs_reflection d hd).2]
  rw [← mul_assoc]

end Algebra

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry
variable (G : TracialCornerGeometry P H)

/-- The bounded map that compresses to the corner and removes its scalar part. -/
def centeredCornerProjection (p : P) : H →L[ℂ] H :=
  G.cornerProjection p p - (G.trace p)⁻¹ • InnerProductSpace.rankOne ℂ (G.vector p) (G.vector p)

/-- Its value on algebra vectors is the centered corner compression. -/
theorem centeredCornerProjection_vector (p : P) (hp : IsStarProjection p) (x : P) :
    G.centeredCornerProjection p (G.vector x) =
      G.vector (p * x * p) - ((G.trace p)⁻¹ * G.trace (p * x)) • G.vector p := by
  simp only [centeredCornerProjection, sub_apply,
    smul_apply, G.cornerProjection_vector, InnerProductSpace.rankOne_apply,
    G.inner_vector, hp.isSelfAdjoint.star_eq, smul_smul]

/-- Every centered corner vector is fixed by the bounded centered compression. -/
theorem centeredCornerProjection_fixed (p : P) (hp : IsStarProjection p)
    (x : CStarCorner p hp) (hx : G.trace (x : P) = 0) :
    G.centeredCornerProjection p (G.vector (x : P)) = G.vector (x : P) := by
  rw [G.centeredCornerProjection_vector p hp, x.property.1, x.property.2, hx]
  simp

/-- The identity contributes only the scalar part of the corner. -/
theorem centeredCornerProjection_one (p : P) (hp : IsStarProjection p)
    (ht : G.trace p ≠ 0) :
    G.centeredCornerProjection p (G.vector 1) = 0 := by
  rw [G.centeredCornerProjection_vector p hp]
  simp only [mul_one, hp.isIdempotentElem.eq, inv_mul_cancel₀ ht, one_smul, sub_self]

/-- All ordinary dihedral rotation and reflection-coset vectors. -/
def dihedralGroupWordVectors (d w : Pˣ) : Set H :=
  Set.range (fun l : ℤ => G.vector (↑(w ^ l) : P)) ∪
    Set.range (fun l : ℤ => G.vector ((↑(w ^ l) : P) * (d : P)))

/-- The normalized Haar and coset moments kill the scalar coefficient of
every nonidentity compressed rotation. -/
theorem trace_halfProjection_rotation (d w : Pˣ)
    (hhaar : ∀ l : ℤ, G.trace (↑(w ^ l) : P) = if l = 0 then 1 else 0)
    (hcoset : ∀ l : ℤ, G.trace ((↑(w ^ l) : P) * (d : P)) = 0)
    (l : ℤ) (hl : l ≠ 0) :
    G.trace (dihedralHalfProjection d * (↑(w ^ l) : P)) = 0 := by
  simp only [dihedralHalfProjection, smul_mul_assoc, add_mul, one_mul,
    map_smul, map_add, G.tracial (d : P), hhaar, ite_eq_right hl, hcoset,
    add_zero, smul_zero]

/-- Reflection does not change the trace coefficient in the corner. -/
theorem trace_halfProjection_coset (d w : Pˣ) (hd : d * d = 1) (l : ℤ) :
    G.trace (dihedralHalfProjection d * ((↑(w ^ l) : P) * (d : P))) =
      G.trace (dihedralHalfProjection d * (↑(w ^ l) : P)) := by
  rw [← mul_assoc, G.tracial _ (d : P), ← mul_assoc,
    (halfProjection_absorbs_reflection d hd).2]

/-- Centered compression sends every group word into the closed span of
positive compressed rotation powers. -/
theorem centeredCornerProjection_group_word_mem
    (d w : Pˣ) (hd : d * d = 1) (hconj : d * w = w⁻¹ * d)
    (hp : IsStarProjection (dihedralHalfProjection d))
    (ht : G.trace (dihedralHalfProjection d) ≠ 0)
    (hhaar : ∀ l : ℤ, G.trace (↑(w ^ l) : P) = if l = 0 then 1 else 0)
    (hcoset : ∀ l : ℤ, G.trace ((↑(w ^ l) : P) * (d : P)) = 0)
    {z : H} (hz : z ∈ G.dihedralGroupWordVectors d w) :
    G.centeredCornerProjection (dihedralHalfProjection d) z ∈
      (Submodule.span ℂ (G.vector '' DihedralCornerWords.positiveCornerPowers
        (dihedralHalfProjection d) (w : P))).topologicalClosure := by
  let M := Submodule.span ℂ (G.vector '' DihedralCornerWords.positiveCornerPowers
    (dihedralHalfProjection d) (w : P))
  have hrot : ∀ l : ℤ,
      G.centeredCornerProjection (dihedralHalfProjection d) (G.vector (↑(w ^ l) : P)) ∈
        M.topologicalClosure := by
    intro l
    by_cases hl : l = 0
    · subst l
      simpa only [zpow_zero, Units.val_one] using
        (show G.centeredCornerProjection (dihedralHalfProjection d) (G.vector 1) ∈
          M.topologicalClosure by rw [G.centeredCornerProjection_one _ hp ht]; exact Submodule.zero_mem _)
    · rw [G.centeredCornerProjection_vector _ hp,
        G.trace_halfProjection_rotation d w hhaar hcoset l hl, mul_zero, zero_smul, sub_zero,
        halfProjection_compressed_natAbs d w hd hconj]
      apply M.le_topologicalClosure
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      exact ⟨⟨l.natAbs, Int.natAbs_pos.mpr hl⟩, rfl⟩
  rcases hz with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · exact hrot l
  · have heq : G.centeredCornerProjection (dihedralHalfProjection d)
        (G.vector ((↑(w ^ l) : P) * (d : P))) =
      G.centeredCornerProjection (dihedralHalfProjection d) (G.vector (↑(w ^ l) : P)) := by
      rw [G.centeredCornerProjection_vector _ hp, G.centeredCornerProjection_vector _ hp,
        halfProjection_compressed_coset d w hd,
        G.trace_halfProjection_coset d w hd]
    rw [heq]
    exact hrot l

/-- Applying the centered corner map to the raw group-word L²-span gives
the desired positive-power density for each centered corner vector. -/
theorem positive_corner_density_of_group_word_density
    (d w : Pˣ) (hd : d * d = 1) (hconj : d * w = w⁻¹ * d)
    (hp : IsStarProjection (dihedralHalfProjection d))
    (ht : G.trace (dihedralHalfProjection d) ≠ 0)
    (hhaar : ∀ l : ℤ, G.trace (↑(w ^ l) : P) = if l = 0 then 1 else 0)
    (hcoset : ∀ l : ℤ, G.trace ((↑(w ^ l) : P) * (d : P)) = 0)
    (x : CStarCorner (dihedralHalfProjection d) hp) (hx : G.trace (x : P) = 0)
    (hspan : G.vector (x : P) ∈
      (Submodule.span ℂ (G.dihedralGroupWordVectors d w)).topologicalClosure) :
    G.vector (x : P) ∈
      (Submodule.span ℂ (G.vector '' DihedralCornerWords.positiveCornerPowers
        (dihedralHalfProjection d) (w : P))).topologicalClosure := by
  let M := (Submodule.span ℂ (G.vector '' DihedralCornerWords.positiveCornerPowers
    (dihedralHalfProjection d) (w : P))).topologicalClosure
  let Q := G.centeredCornerProjection (dihedralHalfProjection d)
  have hmap : Submodule.span ℂ (G.dihedralGroupWordVectors d w) ≤ M.comap Q.toLinearMap := by
    apply Submodule.span_le.mpr
    intro z hz
    exact G.centeredCornerProjection_group_word_mem d w hd hconj hp ht hhaar hcoset hz
  have hM : IsClosed (M : Set H) := Submodule.isClosed_topologicalClosure _
  have hclosed : IsClosed (M.comap Q.toLinearMap : Set H) :=
    hM.preimage Q.continuous
  have h := ((Submodule.span ℂ (G.dihedralGroupWordVectors d w)).topologicalClosure_minimal
    hmap hclosed) hspan
  change Q (G.vector (x : P)) ∈ M at h
  dsimp only [Q] at h
  rw [G.centeredCornerProjection_fixed _ hp x hx] at h
  exact h

/-- For two involutions, the first one reverses their product. -/
theorem free_symmetry_rotation_conjugation (d s : Pˣ)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s) : d * (d * s) = (d * s)⁻¹ * d := by
  have hdd : d * d = 1 := by simpa only [hdi] using inv_mul_cancel d
  calc
    d * (d * s) = s := by rw [← mul_assoc, hdd, one_mul]
    _ = (d * s)⁻¹ * d := by
      rw [mul_inv_rev, hdi, hsi, mul_assoc, hdd, mul_one]

/-- The reflection-coset moments used by the centered corner map follow
from the scalar-freeness moments. -/
theorem free_symmetry_first_coset_moments
    (D A : StarSubalgebra ℂ P) (hf : ScalarFree G.trace D A)
    (d s : Pˣ) (hd : (d : P) ∈ D) (hs : (s : P) ∈ A)
    (hd0 : G.trace (d : P) = 0) (hs0 : G.trace (s : P) = 0)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s) (l : ℤ) :
    G.trace ((↑((d * s) ^ l) : P) * (d : P)) = 0 := by
  have hss : s * s = 1 := by simpa only [hsi] using inv_mul_cancel s
  have heq : (d * s) ^ (l + 1) * s = (d * s) ^ l * d := by
    rw [zpow_add, zpow_one, mul_assoc, mul_assoc, hss, mul_one]
  have hval := congrArg (fun u : Pˣ => (u : P)) heq
  simp only [Units.val_mul] at hval
  rw [← hval]
  exact free_symmetry_coset_moments G.trace D A hf d s hd hs hd0 hs0 hdi hsi (l + 1)

/-- The full normalized-corner freeness theorem requires only the raw
L²-span of the dihedral group words, in addition to the original free factors. -/
theorem scalarFree_corner_of_dihedral_word_density
    (D A C : StarSubalgebra ℂ P) (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (d s : Pˣ) (hd : (d : P) ∈ D) (hs : (s : P) ∈ A)
    (hd0 : G.trace (d : P) = 0) (hs0 : G.trace (s : P) = 0)
    (hdi : d⁻¹ = d) (hsi : s⁻¹ = s)
    (hp : IsStarProjection (dihedralHalfProjection d))
    (hpC : dihedralHalfProjection d ∈ C)
    (hspan : ∀ x : CStarCorner (dihedralHalfProjection d) hp, (x : P) ∈ C →
      G.vector (x : P) ∈
        (Submodule.span ℂ (G.dihedralGroupWordVectors d (d * s))).topologicalClosure) :
    ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp G.trace)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D
        (D.smul_mem (D.add_mem D.one_mem hd) (1 / 2 : ℂ)))
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC) := by
  have hdd : d * d = 1 := by simpa only [hdi] using inv_mul_cancel d
  have htval : G.trace (dihedralHalfProjection d) = (1 / 2 : ℂ) := by
    simp only [dihedralHalfProjection, map_smul, map_add, hτ, hd0, add_zero,
      smul_eq_mul, mul_one]
  have ht : G.trace (dihedralHalfProjection d) ≠ 0 := by rw [htval]; norm_num
  apply DihedralCornerWords.scalarFree_corner_of_positive_power_density G D A C hf hd hs hd0 hs0
    (dihedralHalfProjection d) hp _ hpC
    (halfProjection_absorbs_reflection d hdd).1 ht
  intro x hx hx0
  exact G.positive_corner_density_of_group_word_density d (d * s) hdd
    (free_symmetry_rotation_conjugation d s hdi hsi) hp ht
    (free_symmetry_haar_moments G.trace hτ D A hf d s hd hs hd0 hs0 hdi hsi)
    (G.free_symmetry_first_coset_moments D A hf d s hd hs hd0 hs0 hdi hsi)
    x hx0 (hspan x hx)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
