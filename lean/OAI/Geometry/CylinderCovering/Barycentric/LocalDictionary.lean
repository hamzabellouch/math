import OAI.Geometry.CylinderCovering.Barycentric.CanonicalMapDefinitions
import OAI.Geometry.CylinderCovering.Radial.PairedActual

namespace OAI

open Set
open scoped InnerProductSpace
noncomputable section
namespace RadialCoordinates
open CylinderCovering

private lemma Hpos : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
private lemma Hne : Real.sqrt (2:ℝ) ≠ 0 := Hpos.ne'
private lemma Hsq : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)

theorem canonicalEmbedding_norm (z : Space) : ‖canonicalEmbedding z‖ = ‖z‖ := by
  have hs : ‖canonicalEmbedding z‖^2 = ‖z‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_four,Fin.sum_univ_three]
    simp only [canonicalEmbedding,LinearMap.coe_mk,AddHom.coe_mk]
    dsimp
    field_simp
    nlinarith [Hsq]
  nlinarith [norm_nonneg (canonicalEmbedding z),norm_nonneg z]

def canonicalEmbeddingIsometry : Space →ₗᵢ[ℝ] BarycentricSpace :=
  {canonicalEmbedding with norm_map' := canonicalEmbedding_norm}

theorem canonicalScale_pos : 0 < canonicalScale := by
  unfold canonicalScale
  positivity

theorem canonicalToBary_eq (z : Space) :
    canonicalToBary z = canonicalCenter + canonicalScale • canonicalEmbedding z := by
  ext i
  fin_cases i <;>
    simp [canonicalToBary,barycentricPoint,canonicalCenter,canonicalScale,canonicalEmbedding] <;>
    field_simp <;> ring_nf <;> simp <;> ring

theorem angular_point (N j : ℕ) :
    angular (RadialRiemann.point 0 1 N j) = RadialRiemann.point (-1) 1 N j := by
  unfold angular RadialRiemann.point RadialRiemann.step
  ring

theorem angular_mem_cell_iff (N : ℕ) (i : Fin N) (t : ℝ) :
    angular t ∈ RadialRiemann.cell (-1) 1 N i ↔ t ∈ RadialRiemann.cell 0 1 N i := by
  unfold RadialRiemann.cell
  rw [← angular_point N i,← angular_point N (i+1)]
  simp only [mem_Icc,angular]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem angular_tags {N : ℕ} (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged 0 1 N tag) :
    RadialRiemann.IsTagged (-1) 1 N (fun i => angular (tag i)) :=
  fun i => (angular_mem_cell_iff N i (tag i)).mpr (htag i)

theorem angular_inverse (q : ℝ) : angular ((q+1)/2) = q := by unfold angular; ring

theorem inverse_angular (t : ℝ) : (angular t+1)/2 = t := by unfold angular; ring

theorem lowerPoint_toBary (k t S p : ℝ) :
    canonicalToBary (RadialPairedSweep.point
      ((2*S)*angular t+k*(2*p)*RadialCaps.G (angular t)) (2*p)
      (Real.sqrt 2*(-1+2*S+k*(2*p)*angular t))) = firstSweepPoint k t S p := by
  ext i
  fin_cases i <;>
    simp [canonicalToBary,RadialPairedSweep.point,firstSweepPoint,
      barycentricPoint,RadialCaps.G] <;> field_simp [Hne] <;> ring

theorem upperPoint_toBary (k t S p : ℝ) :
    canonicalToBary (RadialPairedSweep.point (2*p)
      ((2*S)*angular t-k*(2*p)*RadialCaps.G (angular t))
      (Real.sqrt 2*(1-2*S+k*(2*p)*angular t))) = secondSweepPoint k t S p := by
  ext i
  fin_cases i <;>
    simp [canonicalToBary,RadialPairedSweep.point,secondSweepPoint,
      barycentricPoint,RadialCaps.G] <;> field_simp [Hne] <;> ring

theorem lowerLocalSweep_image (k : ℝ) (N : ℕ) (i : Fin N) :
    canonicalToBary '' RadialPairedSweep.lowerLocalSweep (Real.sqrt 2) k
      (canonicalCap k) N i = BarycentricFinite.firstLocalSweep k N i := by
  ext z
  constructor
  · rintro ⟨_,⟨q,hq,ρ,hρ,y,hy,rfl⟩,rfl⟩
    have ht : (q+1)/2 ∈ RadialRiemann.cell 0 1 N i := by
      apply (angular_mem_cell_iff N i _).mp
      simpa only [angular_inverse] using hq
    refine ⟨(q+1)/2,ht,ρ/2,⟨by linarith [hρ.1],?_⟩,
      y/2,⟨by linarith [(abs_le.mp hy).1],by linarith [(abs_le.mp hy).2]⟩,?_⟩
    · change ρ/2 ≤ cap k ((q+1)/2)
      have hc := hρ.2
      change ρ ≤ 2*cap k ((q+1)/2) at hc
      linarith
    · have hr : 2*(ρ/2)=ρ := by ring
      have hy : 2*(y/2)=y := by ring
      simpa only [angular_inverse,hr,hy] using lowerPoint_toBary k ((q+1)/2) (ρ/2) (y/2)
  · rintro ⟨t,ht,S,hS,p,hp,rfl⟩
    refine ⟨RadialPairedSweep.point
      ((2*S)*angular t+k*(2*p)*RadialCaps.G (angular t)) (2*p)
      (Real.sqrt 2*(-1+2*S+k*(2*p)*angular t)),?_,lowerPoint_toBary k t S p⟩
    refine ⟨angular t,(angular_mem_cell_iff N i t).mpr ht,2*S,
      ⟨by linarith [hS.1],?_⟩,2*p,?_,rfl⟩
    · simp only [canonicalCap,inverse_angular]
      linarith [hS.2]
    · rw [abs_le]
      constructor <;> linarith [hp.1,hp.2]

theorem upperLocalSweep_image (k : ℝ) (N : ℕ) (i : Fin N) :
    canonicalToBary '' RadialPairedSweep.upperLocalSweep (Real.sqrt 2) k
      (canonicalCap k) N i = BarycentricFinite.secondLocalSweep k N i := by
  ext z
  constructor
  · rintro ⟨_,⟨q,hq,ρ,hρ,y,hy,rfl⟩,rfl⟩
    have ht : (q+1)/2 ∈ RadialRiemann.cell 0 1 N i := by
      apply (angular_mem_cell_iff N i _).mp
      simpa only [angular_inverse] using hq
    refine ⟨(q+1)/2,ht,ρ/2,⟨by linarith [hρ.1],?_⟩,
      y/2,⟨by linarith [(abs_le.mp hy).1],by linarith [(abs_le.mp hy).2]⟩,?_⟩
    · change ρ/2 ≤ cap k ((q+1)/2)
      have hc := hρ.2
      change ρ ≤ 2*cap k ((q+1)/2) at hc
      linarith
    · have hr : 2*(ρ/2)=ρ := by ring
      have hy : 2*(y/2)=y := by ring
      simpa only [angular_inverse,hr,hy] using upperPoint_toBary k ((q+1)/2) (ρ/2) (y/2)
  · rintro ⟨t,ht,S,hS,p,hp,rfl⟩
    refine ⟨RadialPairedSweep.point (2*p)
      ((2*S)*angular t-k*(2*p)*RadialCaps.G (angular t))
      (Real.sqrt 2*(1-2*S+k*(2*p)*angular t)),?_,upperPoint_toBary k t S p⟩
    refine ⟨angular t,(angular_mem_cell_iff N i t).mpr ht,2*S,
      ⟨by linarith [hS.1],?_⟩,2*p,?_,rfl⟩
    · simp only [canonicalCap,inverse_angular]
      linarith [hS.2]
    · rw [abs_le]
      constructor <;> linarith [hp.1,hp.2]

theorem canonicalEmbedding_lower_raw (k t : ℝ) :
    canonicalEmbedding (RadialPairedSweep.point (k*RadialCaps.G (angular t)) 1
      (Real.sqrt 2*k*angular t)) = Real.sqrt 2 • firstDirection k t := by
  ext i
  fin_cases i <;>
    simp [canonicalEmbedding,RadialPairedSweep.point,firstDirection,RadialCaps.G,angular] <;>
    field_simp [Hne] <;> ring_nf <;> simp <;> ring

theorem canonicalEmbedding_upper_raw (k t : ℝ) :
    canonicalEmbedding (RadialPairedSweep.point 1 (-k*RadialCaps.G (angular t))
      (Real.sqrt 2*k*angular t)) = Real.sqrt 2 • BarycentricFinite.secondDirection k t := by
  ext i
  fin_cases i <;>
    simp [canonicalEmbedding,RadialPairedSweep.point,BarycentricFinite.secondDirection,
      RadialCaps.G,angular] <;>
    field_simp [Hne] <;> ring_nf <;> simp <;> ring

private theorem normalized_positive_smul (v : BarycentricSpace) :
    ‖Real.sqrt 2 • v‖⁻¹ • (Real.sqrt 2 • v) = ‖v‖⁻¹ • v := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos Hpos,smul_smul]
  congr 1
  by_cases hn : ‖v‖ = 0
  · simp [hn]
  · field_simp [Hne,hn]

theorem canonicalEmbedding_lowerAxis (k t : ℝ) :
    canonicalEmbedding (RadialPairedSweep.lowerAxis (Real.sqrt 2) k (angular t)) =
      BarycentricFinite.firstAxis k t := by
  unfold RadialPairedSweep.lowerAxis
  dsimp only
  rw [map_smul,← canonicalEmbedding_norm,canonicalEmbedding_lower_raw]
  exact normalized_positive_smul _

theorem canonicalEmbedding_upperAxis (k t : ℝ) :
    canonicalEmbedding (RadialPairedSweep.upperAxis (Real.sqrt 2) k (angular t)) =
      BarycentricFinite.secondAxis k t := by
  unfold RadialPairedSweep.upperAxis
  dsimp only
  rw [map_smul,← canonicalEmbedding_norm,canonicalEmbedding_upper_raw]
  exact normalized_positive_smul _

theorem canonicalScale_sq : canonicalScale^2 = (1/8 : ℝ) := by
  unfold canonicalScale
  rw [div_pow,mul_pow,Hsq]
  norm_num

theorem canonicalCap_continuous (k : ℝ) : Continuous (canonicalCap k) := by
  unfold canonicalCap cap capPolynomial angular
  fun_prop

theorem canonicalCap_nonneg (k q : ℝ) : 0 ≤ canonicalCap k q := by
  unfold canonicalCap cap capPolynomial
  positivity

theorem barycentric_midpoint_tagged (N : ℕ) :
    RadialRiemann.IsTagged 0 1 N (BarycentricFinite.midpoint N) := by
  intro i
  obtain ⟨t,ht⟩ := RadialRiemann.cell_nonempty (show (0:ℝ)<1 by norm_num) i
  have hle := ht.1.trans ht.2
  change RadialRiemann.point 0 1 N i ≤ _ ∧ _ ≤ RadialRiemann.point 0 1 N (i+1)
  unfold BarycentricFinite.midpoint
  constructor <;> linarith

theorem canonical_midpoint_tagged (N : ℕ) :
    RadialRiemann.IsTagged (-1) 1 N (fun i => angular (BarycentricFinite.midpoint N i)) :=
  angular_tags _ (barycentric_midpoint_tagged N)

theorem canonicalCap_eq (k q : ℝ) :
    canonicalCap k q = 1+k^2*((q^2+q^4)/2+1/500) := by
  unfold canonicalCap cap capPolynomial angular
  ring

theorem canonical_physicalCost (k : ℝ) :
    RadialPairedSweep.physicalCost (Real.sqrt 2) k (canonicalCap k) =
      ∫ q in (-1:ℝ)..1,
        (1+k^2*((q^2+q^4)/2+1/500))^2 /
          (2*Real.sqrt (1+k^2*(2*q^2+((1+q^2)/2)^2))) := by
  unfold RadialPairedSweep.physicalCost
  apply intervalIntegral.integral_congr
  intro q _
  dsimp only
  rw [canonicalCap_eq]
  have hd : RadialCaps.G q^2+(Real.sqrt 2)^2*q^2 =
      2*q^2+((1+q^2)/2)^2 := by rw [Hsq]; unfold RadialCaps.G; ring
  rw [hd]

end RadialCoordinates

end

end OAI
