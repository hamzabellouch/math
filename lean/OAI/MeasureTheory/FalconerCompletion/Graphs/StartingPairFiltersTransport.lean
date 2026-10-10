import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.CompletionPolynomialSubpower

namespace OAI

/-! Graph energies and pair estimates. -/

section

namespace CurrentFalconer.AssemblyCompletion
open Set Metric MeasureTheory Filter
open scoped ENNReal
variable {n : ℕ}

lemma startingPairFilters_transport (f : Space n ≃ₜ Space n)
    (hf : ∀ x y, direction (f x) (f y)=direction x y)
    (μ ν : Measure (Space n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E₁ E₂ : Set (Space n)) (h : StartingPairFilters n μ ν E₁ E₂) :
    StartingPairFilters n (μ.map f) (ν.map f) (f '' E₁) (f '' E₂) := by
  classical
  let F := f.prodCongr f
  have mapF : (μ.map f).prod (ν.map f)=(μ.prod ν).map F :=
    Measure.map_prod_map μ ν f.continuous.measurable f.continuous.measurable
  have mapf (ρ : Measure (Space n)) (S : Set (Space n)) :
      (ρ.map f) S=ρ (f ⁻¹' S) := f.toMeasurableEquiv.map_apply S
  have mapF_apply (S : Set (Space n × Space n)) :
      ((μ.prod ν).map F) S=(μ.prod ν) (F ⁻¹' S) := F.toMeasurableEquiv.map_apply S
  have memF (x y : Space n) (S : Set (Space n × Space n)) :
      (f x,f y)∈F '' S ↔ (x,y)∈S := by
    change F (x,y)∈F '' S ↔ (x,y)∈S
    exact F.injective.mem_set_image
  have hprod (X Y : Set (Space n)) : (f '' X) ×ˢ (f '' Y)=F '' (X ×ˢ Y) := by
    ext ⟨zx,zy⟩
    simp only [mem_prod,mem_image]
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩
      exact ⟨(x,y),⟨hx,hy⟩,rfl⟩
    · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,hxy⟩
      exact ⟨⟨x,hx,congrArg Prod.fst hxy⟩,⟨y,hy,congrArg Prod.snd hxy⟩⟩
  have hfilter (I : Finset ℕ) (X Y : ℕ → Set (Space n)) :
      productFilter I (fun l=>f '' X l) (fun l=>f '' Y l)=F '' productFilter I X Y := by
    simp only [productFilter,image_iUnion,←hprod]
  obtain ⟨omega₀,homega₀,h⟩ := h
  refine ⟨omega₀,homega₀,?_⟩
  intro omega homega homega₀'
  obtain ⟨I,X,Y,A,K,hA,hm,hs,hd,hc,ha,hpos,hcaps⟩ := h omega homega homega₀'
  refine ⟨I,fun N l=>f '' X N l,fun N l=>f '' Y N l,A,K,hA,?_,?_,?_,hc,?_,?_,?_⟩
  · intro N l hl
    exact ⟨f.toMeasurableEquiv.measurableSet_image.mpr (hm N l hl).1,
      f.toMeasurableEquiv.measurableSet_image.mpr (hm N l hl).2⟩
  · intro N l hl
    exact ⟨image_mono (hs N l hl).1,image_mono (hs N l hl).2⟩
  · intro N l hl m hm hlm
    rw [hprod,hprod]
    exact (hd N hl hm hlm).image F.injective.injOn (subset_univ _) (subset_univ _)
  · intro N M hNM
    dsimp only
    rw [hfilter,hfilter]
    exact image_mono (ha hNM)
  · simp only [hfilter,←image_iInter F.bijective,mapF]
    rw [mapF_apply,F.injective.preimage_image]
    exact hpos
  · intro e he
    obtain ⟨c,C,hc,hC,L,hL⟩ := hcaps e he
    refine ⟨c,C,hc,hC,L,?_⟩
    intro N hN
    obtain ⟨G,hG,hGsub,hbad,hcap₁,hcap₂⟩ := hL N hN
    refine ⟨F '' G,F.toMeasurableEquiv.measurableSet_image.mpr hG,?_,?_,?_,?_⟩
    · rw [hfilter]
      exact image_mono hGsub
    · rw [hfilter,←image_sdiff F.injective,mapF,mapF_apply,
        F.injective.preimage_image]
      exact hbad
    · apply f.toMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
      filter_upwards [hcap₁] with x hx
      intro w hw r hr hr1
      rw [mapf]
      change ν {y | (f x,f y)∈F '' G ∧ direction (f x) (f y)∈ball w r} ≤ _
      simpa only [memF,hf] using hx w hw r hr hr1
    · apply f.toMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
      filter_upwards [hcap₂] with y hy
      intro w hw r hr hr1
      rw [mapf]
      change μ {x | (f x,f y)∈F '' G ∧ direction (f x) (f y)∈ball w r} ≤ _
      simpa only [memF,hf] using hy w hw r hr hr1
end CurrentFalconer.AssemblyCompletion
end

section

namespace CurrentFalconer.AssemblyCompletion
open Set Metric MeasureTheory
open scoped ENNReal
variable {n : ℕ}
noncomputable def pairSimilarity (a : ℝ) (ha : a ≠ 0) (b : Space n) : Space n ≃ₜ Space n :=
  (Homeomorph.smul (Units.mk0 a ha)).trans (Homeomorph.addRight b)
lemma pairSimilarity_apply (a : ℝ) (ha : a ≠ 0) (b x : Space n) :
    pairSimilarity a ha b x=a • x+b := rfl
lemma pairSimilarity_dist (a : ℝ) (ha : 0<a) (b x y : Space n) :
    dist (pairSimilarity a ha.ne' b x) (pairSimilarity a ha.ne' b y)=a*dist x y := by
  simp only [pairSimilarity_apply,dist_add_right,dist_smul₀,Real.norm_eq_abs,abs_of_pos ha]
lemma pairSimilarity_direction (a : ℝ) (ha : 0<a) (b x y : Space n) :
    direction (pairSimilarity a ha.ne' b x) (pairSimilarity a ha.ne' b y)=direction x y := by
  rw [direction,pairSimilarity_dist a ha b x y,pairSimilarity_apply,pairSimilarity_apply,
    add_sub_add_right_eq_sub,←smul_sub,mul_inv_rev,smul_smul]
  simp [direction,ha.ne']
lemma similarity_ball_bound (a : ℝ) (ha : 0<a) (b : Space n)
    (μ : Measure (Space n)) (s C : ℝ) (_hC : 0≤C)
    (hμ : ∀ x : Space n, ∀ r>0, μ (ball x r)≤ENNReal.ofReal (C*r^s)) :
    ∀ x : Space n, ∀ r>0, (μ.map (pairSimilarity a ha.ne' b)) (ball x r)≤
      ENNReal.ofReal ((C*a^(-s))*r^s) := by
  intro x r hr
  let f := pairSimilarity a ha.ne' b
  change (μ.map f) (ball x r) ≤ _
  rw [show (μ.map f) (ball x r)=μ (f ⁻¹' ball x r) from
    f.toMeasurableEquiv.map_apply (ball x r)]
  have he : f ⁻¹' ball x r=ball (f.symm x) (r/a) := by
    ext y
    simp only [mem_preimage,mem_ball]
    have hd : dist (f y) x=a*dist y (f.symm x) := by
      calc dist (f y) x=dist (f y) (f (f.symm x)) := by rw [f.apply_symm_apply]
           _=a*dist y (f.symm x) := pairSimilarity_dist a ha b y (f.symm x)
    rw [hd,lt_div_iff₀ ha,mul_comm]
  rw [he]
  have h := hμ (f.symm x) (r/a) (div_pos hr ha)
  have hp : C*(r/a)^s=(C*a^(-s))*r^s := by
    rw [Real.div_rpow hr.le ha.le,Real.rpow_neg ha.le]
    ring
  rw [hp] at h
  exact h
lemma exists_root_similarity (E : Set (Space n)) (hE : IsCompact E) :
    ∃ (a : ℝ) (ha : 0<a) (b : Space n),
      ∀ x∈E, ∀ i, 0≤(pairSimilarity a ha.ne' b x) i ∧
        (pairSimilarity a ha.ne' b x) i<1 := by
  obtain ⟨R,hR,hbound⟩ := hE.isBounded.exists_pos_norm_le
  let a : ℝ := (4*R)⁻¹
  have ha : 0<a := inv_pos.mpr (by positivity)
  let b : Space n := WithLp.toLp 2 (fun _=>1/2)
  refine ⟨a,ha,b,?_⟩
  intro x hx i
  have hxi : |x i|≤R := (PiLp.norm_apply_le x i).trans (hbound x hx)
  have hmul : a*R=1/4 := by dsimp [a]; field_simp
  have hlo : -R≤x i := (abs_le.mp hxi).1
  have hhi : x i≤R := (abs_le.mp hxi).2
  have hlow := mul_le_mul_of_nonneg_left hlo ha.le
  have hhigh := mul_le_mul_of_nonneg_left hhi ha.le
  change 0≤a*x i+1/2 ∧ a*x i+1/2<1
  constructor <;> nlinarith
end CurrentFalconer.AssemblyCompletion
end

end OAI
