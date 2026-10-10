import OAI.Geometry.CylinderCovering.Singular.EdgeOneCoverDefinitions
import OAI.Geometry.CylinderCovering.Singular.Endpoint
import OAI.Geometry.CylinderCovering.Singular.EdgeOne
import OAI.Geometry.CylinderCovering.Ruled.Similarity

namespace OAI

noncomputable section
open Set MeasureTheory Filter Topology
namespace CylinderCovering.SingularEdgeOneCover
open RuledApproximation

lemma height_eq : height = Real.sqrt 2 / 2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold height
  field_simp
  nlinarith

def swap : Space ≃ₗᵢ[ℝ] Space where
  toFun z := vec3 (z 1) (z 0) (z 2)
  invFun z := vec3 (z 1) (z 0) (z 2)
  left_inv z := by ext i; fin_cases i <;> simp [vec3]
  right_inv z := by ext i; fin_cases i <;> simp [vec3]
  map_add' z w := by ext i; fin_cases i <;> simp [vec3]
  map_smul' c z := by ext i; fin_cases i <;> simp [vec3]
  norm_map' z := by
    change ‖vec3 (z 1) (z 0) (z 2)‖ = ‖z‖
    have hz : z = vec3 (z 0) (z 1) (z 2) := by ext i; fin_cases i <;> rfl
    have hs : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
      conv_lhs => rw [hz,norm_vec3_sq]
    have ht := norm_vec3_sq (z 1) (z 0) (z 2)
    nlinarith [norm_nonneg z,norm_nonneg (vec3 (z 1) (z 0) (z 2))]

lemma map_eq_similarity : map = Similarity.map 0 (1/2) swap := by
  funext z
  ext i
  fin_cases i <;> simp [map,Similarity.map,swap,vec3] <;> ring

lemma map_inverse (z : Space) : map (vec3 (2*z 1) (2*z 0) (2*z 2)) = z := by
  ext i
  fin_cases i <;> simp [map,vec3]

lemma map_image_tetrahedron : map '' RuledApproximation.tetrahedron = tetrahedron := by
  ext z
  constructor
  · rintro ⟨w,⟨t,ht0,ht1,hx,hy,hz⟩,rfl⟩
    refine ⟨t,ht0,ht1,?_,?_,?_⟩
    · change |w 1/2| ≤ t/2
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    · change |w 0/2| ≤ (1-t)/2
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    · change w 2/2 = height*t
      rw [hz,height_eq]
      ring
  · rintro ⟨t,ht0,ht1,hx,hy,hz⟩
    refine ⟨vec3 (2*z 1) (2*z 0) (2*z 2),⟨t,ht0,ht1,?_,?_,?_⟩,map_inverse z⟩
    · change |2*z 1| ≤ 1-t
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    · change |2*z 0| ≤ t
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    · change 2*z 2 = Real.sqrt 2*t
      rw [hz,height_eq]
      ring

lemma map_image_lowerTip (d : ℝ) : map '' RuledApproximation.lowerTip d = lowerTip d := by
  ext z
  constructor
  · rintro ⟨w,⟨t,ht0,ht1,hy,hz⟩,rfl⟩
    refine ⟨t,ht0,ht1,?_,?_⟩
    · change |w 1/2| ≤ t/2
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    · change w 2/2 = height*t
      rw [hz,height_eq]
      ring
  · rintro ⟨t,ht0,ht1,hx,hz⟩
    refine ⟨vec3 (2*z 1) (2*z 0) (2*z 2),⟨t,ht0,ht1,?_,?_⟩,map_inverse z⟩
    · change |2*z 0| ≤ t
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    · change 2*z 2 = Real.sqrt 2*t
      rw [hz,height_eq]
      ring

lemma map_image_upperTip (d : ℝ) : map '' RuledApproximation.upperTip d = upperTip d := by
  ext z
  constructor
  · rintro ⟨w,⟨t,ht0,ht1,hx,hz⟩,rfl⟩
    refine ⟨t,ht0,ht1,?_,?_⟩
    · change |w 0/2| ≤ t/2
      rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    · change w 2/2 = height*(1-t)
      rw [hz,height_eq]
      ring
  · rintro ⟨t,ht0,ht1,hy,hz⟩
    refine ⟨vec3 (2*z 1) (2*z 0) (2*z 2),⟨t,ht0,ht1,?_,?_⟩,map_inverse z⟩
    · change |2*z 1| ≤ t
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    · change 2*z 2 = Real.sqrt 2*(1-t)
      rw [hz,height_eq]
      ring

lemma ceiling_eq (p w : ℝ) : ceilingPolynomial p w = SingularEdgeOne.ceiling p w := by
  unfold ceilingPolynomial SingularEdgeOne.ceiling
  ring

lemma fieldP_eq (p : ℝ) (b : Plane) : singularField p b 0 = SingularEdgeOne.fieldP p (b 0) (b 1) := by
  simp only [singularField,vec2_apply_zero,SingularEdgeOne.fieldP]
  congr 2 <;> ring_nf

lemma fieldQ_eq (p : ℝ) (b : Plane) : singularField p b 1 = SingularEdgeOne.fieldQ p (b 0) (b 1) := by
  simp only [singularField,vec2_apply_one,SingularEdgeOne.fieldQ]
  congr 2
  ring

lemma label_dictionary {p c d q : ℝ}
    (hcap : ∀ b ∈ FlexibleSingular.labelDomain p c d q, b 1 ≤ 1) (b : Plane) :
    vec2 (b 0/2) (b 1) ∈ labelDomain p (4*c) d q ↔
      b ∈ FlexibleSingular.labelDomain p c d q := by
  have he := SingularEdgeOne.ceiling_dictionary p (b 0) c (b 1) q
  rw [← ceiling_eq] at he
  change (d ≤ b 1 ∧ b 1 ≤ 1 ∧ |b 0/2| ≤ b 1/2 ∧
    b 1 ≤ 1/2+(4*c)^2*SingularEdgeOne.edgeCeiling p (b 0/2)+q) ↔ _
  rw [SingularEdgeOne.cone_dictionary,← he]
  constructor
  · rintro ⟨hd,h1,hcone,hceil⟩
    exact ⟨hd,h1.trans (by norm_num),hcone,hceil⟩
  · intro hb
    exact ⟨hb.1,hcap b hb,hb.2.2.1,hb.2.2.2⟩

lemma edgeU_label (p : ℝ) (b : Plane) :
    SingularEdgeOne.edgeU p (b 0/2) (b 1) = singularField p b 0 / 4 := by
  rw [SingularEdgeOne.edgeU_eq,fieldP_eq]
  congr 2
  ring

lemma edgeV_label (p : ℝ) {b : Plane} (hb : 0 < b 1) :
    SingularEdgeOne.edgeV p (b 0/2) (b 1) = singularField p b 1 / 2 := by
  rw [SingularEdgeOne.edgeV_eq p _ hb,fieldQ_eq]
  congr 2
  ring

lemma map_lower_parameter (p c x : ℝ) {b : Plane} (hb : 0 < b 1) :
    map (vec3 x (b 0+x*(c*singularField p b 0))
      (Real.sqrt 2*(b 1+x*(c*singularField p b 1)))) =
    vec3 (b 0/2+(4*c)*(x/2)*SingularEdgeOne.edgeU p (b 0/2) (b 1)) (x/2)
      (height*(b 1+(4*c)*(x/2)*SingularEdgeOne.edgeV p (b 0/2) (b 1))) := by
  rw [edgeU_label,edgeV_label p hb,height_eq]
  ext i
  fin_cases i <;> simp [map,vec3] <;> ring

lemma map_upper_parameter (p c y : ℝ) {b : Plane} (hb : 0 < b 1) :
    map (vec3 (b 0-c*y*singularField p b 0) y
      (Real.sqrt 2*(1-(b 1-c*y*singularField p b 1)))) =
    vec3 (y/2) (b 0/2-(4*c)*(y/2)*SingularEdgeOne.edgeU p (b 0/2) (b 1))
      (height*(1-(b 1-(4*c)*(y/2)*SingularEdgeOne.edgeV p (b 0/2) (b 1)))) := by
  rw [edgeU_label,edgeV_label p hb,height_eq]
  ext i
  fin_cases i <;> simp [map,vec3] <;> ring

lemma label_expand_contract (b : Plane) :
    vec2 ((vec2 (2*b 0) (b 1)) 0/2) ((vec2 (2*b 0) (b 1)) 1) = b := by
  ext i
  fin_cases i <;> simp [vec2]

lemma map_image_lowerFamily {p c d q : ℝ} (hd : 0 < d)
    (hcap : ∀ b ∈ FlexibleSingular.labelDomain p c d q, b 1 ≤ 1) :
    map '' FlexibleSingular.lowerFamily p c d q = lowerFamily p (4*c) d q := by
  ext z
  constructor
  · rintro ⟨w,⟨b,hb,x,hx,rfl⟩,rfl⟩
    refine ⟨vec2 (b 0/2) (b 1),(label_dictionary hcap b).mpr hb,x/2,?_,?_⟩
    · rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    · exact map_lower_parameter p c x (hd.trans_le hb.1)
  · rintro ⟨b,hb,y,hy,rfl⟩
    let b' := vec2 (2*b 0) (b 1)
    have hb' : b' ∈ FlexibleSingular.labelDomain p c d q := by
      apply (label_dictionary hcap b').mp
      simpa only [b',label_expand_contract] using hb
    have hy' : |2*y| ≤ 1 := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    refine ⟨vec3 (2*y) (b' 0+(2*y)*(c*singularField p b' 0))
      (Real.sqrt 2*(b' 1+(2*y)*(c*singularField p b' 1))),
      ⟨b',hb',2*y,hy',rfl⟩,?_⟩
    rw [map_lower_parameter p c (2*y) (hd.trans_le hb'.1)]
    simp [b',vec2]

lemma map_image_upperFamily {p c d q : ℝ} (hd : 0 < d)
    (hcap : ∀ b ∈ FlexibleSingular.labelDomain p c d q, b 1 ≤ 1) :
    map '' FlexibleSingular.upperFamily p c d q = upperFamily p (4*c) d q := by
  ext z
  constructor
  · rintro ⟨w,⟨b,hb,y,hy,rfl⟩,rfl⟩
    refine ⟨vec2 (b 0/2) (b 1),(label_dictionary hcap b).mpr hb,y/2,?_,?_⟩
    · rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    · exact map_upper_parameter p c y (hd.trans_le hb.1)
  · rintro ⟨b,hb,x,hx,rfl⟩
    let b' := vec2 (2*b 0) (b 1)
    have hb' : b' ∈ FlexibleSingular.labelDomain p c d q := by
      apply (label_dictionary hcap b').mp
      simpa only [b',label_expand_contract] using hb
    have hx' : |2*x| ≤ 1 := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    refine ⟨vec3 (b' 0-c*(2*x)*singularField p b' 0) (2*x)
      (Real.sqrt 2*(1-(b' 1-c*(2*x)*singularField p b' 1))),
      ⟨b',hb',2*x,hx',rfl⟩,?_⟩
    rw [map_upper_parameter p c (2*x) (hd.trans_le hb'.1)]
    simp [b',vec2]

lemma half_ne : (1/2 : ℝ) ≠ 0 := by norm_num

lemma transport_carrier (C : Cylinder) :
    (C.similarity 0 half_ne swap).carrier = map '' C.carrier := by
  rw [Cylinder.similarity_carrier,← map_eq_similarity]

lemma transport_familySet {n : ℕ} (C : Fin n → Cylinder) :
    familySet (fun i => (C i).similarity 0 half_ne swap) = map '' familySet C := by
  rw [similarity_familySet,← map_eq_similarity]

lemma transport_zero_tendsto :
    Tendsto (fun k : ℝ => k/4) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h0 : Tendsto (fun k : ℝ => k) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h0.div_const 4
  · filter_upwards [self_mem_nhdsWithin] with k hk
    change 0 < k/4
    exact div_pos (show 0 < k from hk) (by norm_num)

theorem alternative_cover : AlternativeStatement := by
  intro p β hp hp' hβ hβp
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 51 by norm_num)
  have hn := Real.sqrt_nonneg (51:ℝ)
  have hp2 : p < 2 := by nlinarith
  have hadm := SingularCutoff.edge_one_alternative_admissible hp2 hβ hβp
  have hmain := (FlexibleSingular.flexible_singular p
    (SingularCutoff.powerCutoff 4 β) (SingularCutoff.powerPadding 4 1 (5/2)) hp hp' hadm).2.2
  have hdom := FlexibleSingular.labelDomain_eq_upper_one hadm
  filter_upwards [transport_zero_tendsto.eventually hmain,
    transport_zero_tendsto.eventually hdom,self_mem_nhdsWithin] with k hk hdomk hk0
  have hk0 : 0 < k := hk0
  have he4 : 4*(k/4) = k := by ring
  simp only [SingularCutoff.powerCutoff,SingularCutoff.powerPadding,one_mul,he4] at hk hdomk
  have hd : 0 < k^β := Real.rpow_pos_of_pos hk0 β
  have hcap : ∀ b ∈ FlexibleSingular.labelDomain p (k/4) (k^β) (k^(5/2:ℝ)), b 1 ≤ 1 := by
    intro b hb
    rw [hdomk] at hb
    exact hb.2.1
  have hlower := map_image_lowerFamily hd hcap
  have hupper := map_image_upperFamily hd hcap
  rw [he4] at hlower hupper
  obtain ⟨n,m,C,D,B₁,B₂,hC,hD,hB₁,hB₂,hcovC,hcovD,hcar₁,hcar₂,harea₁,harea₂,hcover,hcost⟩ := hk
  refine ⟨n,m,(fun i => (C i).similarity 0 half_ne swap),
    (fun i => (D i).similarity 0 half_ne swap),B₁.similarity 0 half_ne swap,
    B₂.similarity 0 half_ne swap,
    (fun i => Cylinder.similarity_parallelogram (hC i) 0 half_ne swap),
    (fun i => Cylinder.similarity_parallelogram (hD i) 0 half_ne swap),
    Cylinder.similarity_triangle hB₁ 0 half_ne swap,
    Cylinder.similarity_triangle hB₂ 0 half_ne swap,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [transport_familySet,← hlower]
    exact image_mono hcovC
  · rw [transport_familySet,← hupper]
    exact image_mono hcovD
  · rw [transport_carrier,hcar₁,map_image_lowerTip]
  · rw [transport_carrier,hcar₂,map_image_upperTip]
  · rw [Cylinder.similarity_area,harea₁,height_eq]
    ring
  · rw [Cylinder.similarity_area,harea₂,height_eq]
    ring
  · rw [← map_image_tetrahedron,transport_familySet,transport_familySet,
      transport_carrier,transport_carrier,← image_union,← image_union,← image_union]
    exact image_mono hcover
  · rw [similarity_familyArea,similarity_familyArea,Cylinder.similarity_area,
      Cylinder.similarity_area,height_eq]
    nlinarith only [hcost]

theorem flexible_cover : FlexibleStatement := by
  intro p ρ q hp hp' hadm
  have hmain := (FlexibleSingular.flexible_singular p ρ q hp hp' hadm).2.2
  have hdom := FlexibleSingular.labelDomain_eq_upper_one hadm
  filter_upwards [transport_zero_tendsto.eventually hmain,
    transport_zero_tendsto.eventually hdom,
    transport_zero_tendsto.eventually hadm.1] with k hk hdomk hpos
  have hd : 0 < ρ (k/4) := hpos.1
  have hcap : ∀ b ∈ FlexibleSingular.labelDomain p (k/4) (ρ (k/4)) (q (k/4)),
      b 1 ≤ 1 := by
    intro b hb
    rw [hdomk] at hb
    exact hb.2.1
  have he4 : 4*(k/4) = k := by ring
  have hlower := map_image_lowerFamily hd hcap
  have hupper := map_image_upperFamily hd hcap
  rw [he4] at hlower hupper
  obtain ⟨n,m,C,D,B₁,B₂,hC,hD,hB₁,hB₂,hcovC,hcovD,hcar₁,hcar₂,harea₁,harea₂,hcover,hcost⟩ := hk
  refine ⟨n,m,(fun i => (C i).similarity 0 half_ne swap),
    (fun i => (D i).similarity 0 half_ne swap),B₁.similarity 0 half_ne swap,
    B₂.similarity 0 half_ne swap,
    (fun i => Cylinder.similarity_parallelogram (hC i) 0 half_ne swap),
    (fun i => Cylinder.similarity_parallelogram (hD i) 0 half_ne swap),
    Cylinder.similarity_triangle hB₁ 0 half_ne swap,
    Cylinder.similarity_triangle hB₂ 0 half_ne swap,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [transport_familySet,← hlower]
    exact image_mono hcovC
  · rw [transport_familySet,← hupper]
    exact image_mono hcovD
  · rw [transport_carrier,hcar₁,map_image_lowerTip]
  · rw [transport_carrier,hcar₂,map_image_upperTip]
  · rw [Cylinder.similarity_area,harea₁,height_eq]
    ring
  · rw [Cylinder.similarity_area,harea₂,height_eq]
    ring
  · rw [← map_image_tetrahedron,transport_familySet,transport_familySet,
      transport_carrier,transport_carrier,← image_union,← image_union,← image_union]
    exact image_mono hcover
  · rw [similarity_familyArea,similarity_familyArea,Cylinder.similarity_area,
      Cylinder.similarity_area,height_eq]
    nlinarith only [hcost]

theorem exact_cover : ExactStatement := by
  intro p γ hp hp' hγ hγp
  have hs := Real.sq_sqrt (show (0:ℝ)≤51 by norm_num)
  have hn := Real.sqrt_nonneg (51:ℝ)
  have hp2 : p < 2 := by nlinarith
  have hγbound : 0 < 1+γ*(p-2) := by
    have h := (lt_div_iff₀ (sub_pos.mpr hp2)).mp hγp
    nlinarith
  have hadm := SingularCutoff.power_admissible
    (A := 1) (B := 1) (p := p) (β := γ) (η := 5/2)
    (by norm_num) (by norm_num) hγ hγbound (by norm_num) (by norm_num)
  have hm := flexible_cover p (SingularCutoff.powerCutoff 1 γ)
    (SingularCutoff.powerPadding 1 1 (5/2)) hp hp' hadm
  filter_upwards [hm,self_mem_nhdsWithin] with k hk hk0
  have hk0 : 0 < k := hk0
  simpa only [SingularCutoff.powerCutoff,SingularCutoff.powerPadding,one_mul,
    SingularEdgeOne.exact_cutoff_dictionary hk0.le γ,
    SingularEdgeOne.exact_padding_dictionary hk0.le] using hk

end CylinderCovering.SingularEdgeOneCover

end

end OAI
