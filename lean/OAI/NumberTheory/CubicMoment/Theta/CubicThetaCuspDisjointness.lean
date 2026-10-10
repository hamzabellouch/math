import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspNeighborhoodCover

namespace OAI

/-! Above height one, two arithmetic cusp neighborhoods are either
identical at every height or disjoint. This removes duplicate cusp
charts before summing the sharp exterior energy inequality. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPointHeight_upper (a : SL(2,Eisenstein)) (ha : a 1 0=0) (p : CubicThetaPoint) :
    cubicThetaPointHeight (a • p)=cubicThetaPointHeight p := by
  have hdet : a 0 0*a 1 1=1 := by
    simpa only [Matrix.det_fin_two,ha,mul_zero,sub_zero] using a.property
  have hu : IsUnit (a 1 1) := isUnit_iff_exists_inv'.mpr ⟨a 0 0,hdet⟩
  have hc : cubicThetaFullComplex a 1 0=0 := congrArg (fun z : Eisenstein => (z:ℂ)) ha
  have hd : Complex.normSq (cubicThetaFullComplex a 1 1)=1 := norm_of_isUnit hu
  change p.val.2/cubicThetaMobiusDenominator (cubicThetaFullComplex a) p.val=p.val.2
  simp only [cubicThetaMobiusDenominator,hc,zero_mul,zero_add,hd,
    Complex.normSq_zero,add_zero,div_one]

lemma cubicThetaCuspNeighborhood_mem_iff (δ : SL(2,Eisenstein)) (H : ℝ)
    (q : CubicThetaQuotient) :
    q∈cubicThetaCuspNeighborhood δ H ↔ ∃ p : CubicThetaPoint,
      H<cubicThetaPointHeight p ∧ cubicThetaQuotientMap (δ • p)=q := by
  constructor
  · rintro ⟨_,⟨p,hp,rfl⟩,he⟩
    exact ⟨p,hp.1,he⟩
  · rintro ⟨p,hp,rfl⟩
    exact cubicThetaCuspNeighborhood_mem_of_height δ p hp

lemma cubicThetaCuspNeighborhood_parabolic_eq (δ ε : SL(2,Eisenstein))
    (g : cubicThetaPrincipalGroup) (a : SL(2,Eisenstein)) (ha : a 1 0=0)
    (he : δ*a=g.val*ε) (H : ℝ) :
    cubicThetaCuspNeighborhood δ H=cubicThetaCuspNeighborhood ε H := by
  have hmap (p : CubicThetaPoint) :
      cubicThetaQuotientMap (δ • (a • p))=cubicThetaQuotientMap (ε • p) := by
    rw [← mul_smul,he,mul_smul]
    change cubicThetaQuotientMap (g • (ε • p))=cubicThetaQuotientMap (ε • p)
    exact cubicThetaQuotient_covering.map_smul g
  ext q
  rw [cubicThetaCuspNeighborhood_mem_iff,cubicThetaCuspNeighborhood_mem_iff]
  constructor
  · rintro ⟨p,hp,hpq⟩
    have hheight : cubicThetaPointHeight (a⁻¹ • p)=cubicThetaPointHeight p := by
      have h := cubicThetaPointHeight_upper a ha (a⁻¹ • p)
      simpa only [smul_inv_smul] using h.symm
    refine ⟨a⁻¹ • p,?_,?_⟩
    · rwa [hheight]
    · have h := hmap (a⁻¹ • p)
      rw [smul_inv_smul,hpq] at h
      exact h.symm
  · rintro ⟨p,hp,hpq⟩
    refine ⟨a • p,?_,(hmap p).trans hpq⟩
    rwa [cubicThetaPointHeight_upper a ha]

theorem cubicThetaCuspNeighborhood_overlap (δ ε : SL(2,Eisenstein))
    {H : ℝ} (hH : 1≤H)
    (hne : (cubicThetaCuspNeighborhood δ H ∩ cubicThetaCuspNeighborhood ε H).Nonempty) :
    ∀ T : ℝ, cubicThetaCuspNeighborhood δ T=cubicThetaCuspNeighborhood ε T := by
  obtain ⟨q,hδ,hε⟩ := hne
  obtain ⟨p,hp,hpq⟩ := (cubicThetaCuspNeighborhood_mem_iff δ H q).mp hδ
  obtain ⟨r,hr,hrq⟩ := (cubicThetaCuspNeighborhood_mem_iff ε H q).mp hε
  have he : cubicThetaQuotientMap (δ • p)=cubicThetaQuotientMap (ε • r) := hpq.trans hrq.symm
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  change g.val • (ε • r)=δ • p at hg
  let a := δ⁻¹*g.val*ε
  have har : a • r=p := by
    dsimp [a]
    rw [mul_smul,mul_smul,hg,inv_smul_smul]
  have hhigh : 1<(cubicThetaMobius (cubicThetaFullComplex a) r.val).2 := by
    change 1<cubicThetaPointHeight (a • r)
    rw [har]
    exact lt_of_le_of_lt hH hp
  have ha : a 1 0=0 := cubicThetaMobius_high_overlap a (lt_of_le_of_lt hH hr) hhigh
  have hrel : δ*a=g.val*ε := by dsimp [a]; group
  exact cubicThetaCuspNeighborhood_parabolic_eq δ ε g a ha hrel

theorem cubicThetaCuspNeighborhood_eq_or_disjoint (δ ε : SL(2,Eisenstein))
    {H : ℝ} (hH : 1≤H) :
    cubicThetaCuspNeighborhood δ H=cubicThetaCuspNeighborhood ε H ∨
      Disjoint (cubicThetaCuspNeighborhood δ H) (cubicThetaCuspNeighborhood ε H) := by
  by_cases h : (cubicThetaCuspNeighborhood δ H ∩ cubicThetaCuspNeighborhood ε H).Nonempty
  · exact Or.inl (cubicThetaCuspNeighborhood_overlap δ ε hH h H)
  · exact Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h))

end CubicFirstMoment

end

end OAI
