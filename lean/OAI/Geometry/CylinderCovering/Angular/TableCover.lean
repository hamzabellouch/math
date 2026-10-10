import OAI.Geometry.CylinderCovering.Angular.TableCoverDefinitions
import OAI.Geometry.CylinderCovering.Angular.Table
import OAI.Geometry.CylinderCovering.Angular.PartitionIdentities
import OAI.Geometry.CylinderCovering.Angular.TableFamilyCosts
import OAI.Geometry.CylinderCovering.Angular.GeneralTheorem
import OAI.Geometry.CylinderCovering.Angular.OrdinaryCaps
import OAI.Geometry.CylinderCovering.Convexity.SquaredCapData
import OAI.Geometry.CylinderCovering.Cartesian.CoverEligibility

namespace OAI

noncomputable section
open Set
namespace CylinderCovering.AngularTableCover
open AngularTable

lemma data_count (cap : Cap) (p : Parameters) : (data cap p).count = p.sectors := by
  cases cap <;> rfl

lemma conclusion_mono {r τ η A B : ℝ} {D : AngularGeneral.Data}
    (h : AngularTableGeometry.Conclusion r τ η A D) (hab : A ≤ B) :
    AngularTableGeometry.Conclusion r τ η B D := by
  rcases h with ⟨hc,hb,hi,he,hs,hr,ht⟩
  exact ⟨hc,hb,hi,he.trans (mul_le_mul_of_nonneg_right hab (by positivity)),hs,hr,ht⟩

lemma row_of_conclusion {cap : Cap} {p : Parameters} {A s Q : ℝ}
    (hA : 0 < A) (hedge : 0 < p.edge) (hτ : 0 < p.tilt)
    (_ : 0 ≤ s) (hts : p.tilt ≤ 2*s) (hQ : quadraticCost p = Q)
    (hτsmall : p.tilt ≤ 1/4) (hη : p.margin ∈ Ioc (0:ℝ) 1)
    (hcap : ∀ b, cap = .cartesian b → b ∈ Icc (3/4:ℝ) 1)
    (hD : AngularGeneral.Admissible p.tilt p.margin 32 (data cap p))
    (h : AngularGeneral.Conclusion p.tilt p.margin A (data cap p)) :
    RowConclusion cap p Q (16*A) s := by
  have hr : p.edge/2 ≠ 0 := (div_pos hedge (by norm_num)).ne'
  have hd := AngularTableGeometry.conclusion_dilate hr h
  have hbound : |normalizedCost cap p - Q| ≤ (16*A)*s^4 := by
    have he := hd.2.2.2.1
    change |normalizedCost cap p - quadraticCost p| ≤ A*p.tilt^4 at he
    rw [hQ] at he
    calc
      _ ≤ A*p.tilt^4 := he
      _ ≤ A*(2*s)^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hτ.le hts 4) hA.le
      _ = _ := by ring
  refine ⟨conclusion_mono hd (by linarith), hbound, data_count cap p, ?_, ?_, ?_, ?_⟩
  · intro hc j hj
    rcases hc with rfl | rfl
    · apply hd.2.2.2.2.2.2 j (by simpa only [data_count] using hj)
      exact ⟨AngularOrdinaryCaps.midpointRadius p.tilt p.margin
        (node p.sectors j) (node p.sectors (j+1)), fun q hq => rfl⟩
    · apply hd.2.2.2.2.2.2 j (by simpa only [data_count] using hj)
      exact ⟨AngularOrdinaryCaps.maximumRadius p.tilt p.margin
        (node p.sectors j) (node p.sectors (j+1)), fun q hq => rfl⟩
  · intro b hb j hj
    subst cap
    have hn : ∀ k ≤ p.sectors, |node p.sectors k| ≤ 1 := hD.2.2.2.2.1
    exact ⟨CartesianCaps.cartesian_lowerIntercept p.tilt p.margin b
      (AngularOrdinaryCaps.ordinaryData .radial p.sectors (node p.sectors) p.tilt p.margin)
      ⟨hτ.le,hτsmall⟩ hη (hcap b rfl) hn j hj,
      CartesianCaps.cartesian_upperIntercept p.tilt p.margin b
      (AngularOrdinaryCaps.ordinaryData .radial p.sectors (node p.sectors) p.tilt p.margin)
      ⟨hτ.le,hτsmall⟩ hη (hcap b rfl) hn j hj⟩
  · have hl := AngularTableGeometry.lower_family_area hr p.tilt (data cap p)
    have hu := AngularTableGeometry.upper_family_area hr p.tilt (data cap p)
    cases cap <;> exact hl.trans hu.symm
  · have hl := AngularTableGeometry.lower_family_area hr p.tilt (data cap p)
    cases cap <;> exact hl

lemma table_admissible {cap : Cap} {p : Parameters}
    (hm : 0 < p.sectors) (hmesh : mesh p ≤ 32*p.tilt^2)
    (hτ : p.tilt ∈ Icc (0:ℝ) (1/4)) (hη : p.margin ∈ Ioc (0:ℝ) (1/480)) :
    AngularGeneral.Admissible p.tilt p.margin 32 (data cap p) := by
  obtain ⟨h0,h1,hinc,hbound,hwidth⟩ := AngularPartitionIdentities.partition_properties hm hmesh
  have ho : ∀ c : AngularOrdinaryCaps.CapChoice, AngularGeneral.Admissible p.tilt p.margin 32
      (AngularOrdinaryCaps.ordinaryData c p.sectors (node p.sectors) p.tilt p.margin) :=
    fun c => AngularOrdinaryCaps.ordinaryData_admissible c hm
      h0 h1 hinc hη.1.le (by norm_num : (0:ℝ) ≤ 32) hwidth
  cases cap with
  | midpoint => exact ho .midpoint
  | maximum => exact ho .maximum
  | radial => exact ho .radial
  | squared =>
    have hmax : max (32:ℝ) ((1/8+p.margin)^2) = 32 := by
      apply max_eq_left
      have hx : (1/8+p.margin)^2 ≤ 1 := by nlinarith [hη.1,hη.2]
      linarith
    dsimp only [data]
    simpa only [hmax] using AngularCaps.withSquaredCaps_admissible hη.1.le (ho .radial)
  | cartesian b =>
    have hc := CartesianCaps.cartesianData_admissible hm h0 h1 hinc hτ
      (show p.margin ∈ Ioc (0:ℝ) 1 from ⟨hη.1,by linarith [hη.2]⟩)
      (by norm_num : (0:ℝ) ≤ 32) hwidth
    norm_num only [max_eq_left (by norm_num : (12:ℝ) ≤ 32)] at hc
    exact hc

lemma uniform_rows (cap : Cap) {η : ℝ} (hη : 0 < η) (hη' : η < 1/480)
    (hcap : ∀ b, cap = .cartesian b → b ∈ Icc (3/4:ℝ) 1) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ ∀ p : Parameters,
      p.margin = η → 0 < p.edge → 0 < p.tilt → p.tilt < δ →
      0 < p.sectors → mesh p ≤ 32*p.tilt^2 →
      ∀ Q s : ℝ, 0 ≤ s → p.tilt ≤ 2*s → quadraticCost p = Q →
      RowConclusion cap p Q A s := by
  obtain ⟨δ,A,hδ,hA,hg⟩ := AngularGeneral.general_cap η hη hη' 32 (by norm_num)
  refine ⟨min δ (1/4),16*A,lt_min hδ (by norm_num),by positivity,?_⟩
  intro p hp hedge hτ ht hm hmesh Q s hs hts hQ
  have hsmall : p.tilt ≤ 1/4 := (ht.trans_le (min_le_right _ _)).le
  have heta : p.margin ∈ Ioc (0:ℝ) (1/480) := by rw [hp]; exact ⟨hη,hη'.le⟩
  have hD := table_admissible (cap := cap) hm hmesh ⟨hτ.le,hsmall⟩ heta
  have hh := hg p.tilt hτ (ht.trans_le (min_le_left _ _)) (data cap p) (by simpa [hp] using hD)
  apply row_of_conclusion hA hedge hτ hs hts hQ hsmall
    ⟨heta.1,by linarith [heta.2]⟩ hcap hD
  simpa [hp] using hh

lemma integer_row (cap : Cap) {η : ℝ} (hη : 0 < η) (hη' : η < 1/480)
    (hcap : ∀ b, cap = .cartesian b → b ∈ Icc (3/4:ℝ) 1)
    (p : ℕ → Parameters) (Q : ℕ → ℝ)
    (hpars : ∀ n : ℕ, 0 < n → (p n).margin = η ∧ 0 < (p n).edge ∧
      0 < (p n).tilt ∧ (p n).tilt ≤ 2/(n:ℝ) ∧ 0 < (p n).sectors ∧
      mesh (p n) ≤ 32*(p n).tilt^2 ∧ quadraticCost (p n) = Q n) :
    IntegerRow cap p Q := by
  obtain ⟨δ,A,hδ,hA,hr⟩ := uniform_rows cap hη hη' hcap
  obtain ⟨N,hN⟩ := exists_nat_gt (2/δ)
  have hNreal : (0:ℝ) < N := (div_pos (by norm_num) hδ).trans hN
  have hNpos : 0 < N := by exact_mod_cast hNreal
  refine ⟨N,A,hNpos,hA,?_⟩
  intro n hn
  have hnpos : 0 < n := hNpos.trans_le hn
  have hnreal : (0:ℝ) < n := by positivity
  have hnlarge : 2/δ < (n:ℝ) := hN.trans_le (by exact_mod_cast hn)
  have htilt : 2/(n:ℝ) < δ := by
    apply (div_lt_iff₀ hnreal).mpr
    have hh := (div_lt_iff₀ hδ).mp hnlarge
    nlinarith only [hh]
  obtain ⟨he,ha,ht,htwo,hm,hmesh,hQ⟩ := hpars n hnpos
  apply hr (p n) he ha ht (htwo.trans_lt htilt) hm hmesh (Q n) (1/(n:ℝ))
    (by positivity) _ hQ
  simpa only [div_eq_mul_inv,one_mul] using htwo

lemma real_row (cap : Cap) {η : ℝ} (hη : 0 < η) (hη' : η < 1/480)
    (hcap : ∀ b, cap = .cartesian b → b ∈ Icc (3/4:ℝ) 1)
    (p : ℝ → Parameters) (Q : ℝ → ℝ)
    (hpars : ∀ t : ℝ, 0 < t → (p t).margin = η ∧ 0 < (p t).edge ∧
      0 < (p t).tilt ∧ (p t).tilt ≤ t ∧ 0 < (p t).sectors ∧
      mesh (p t) ≤ 32*(p t).tilt^2 ∧ quadraticCost (p t) = Q t) :
    RealRow cap p Q := by
  obtain ⟨δ,A,hδ,hA,hr⟩ := uniform_rows cap hη hη' hcap
  refine ⟨δ,A,hδ,hA,?_⟩
  intro t ht htδ
  obtain ⟨he,ha,htilt,htle,hm,hmesh,hQ⟩ := hpars t ht
  exact hr (p t) he ha htilt (htle.trans_lt htδ) hm hmesh (Q t) t ht.le
    (by linarith) hQ

theorem table_covers : Statement := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply integer_row .midpoint (η := 1/1920) (by norm_num) (by norm_num)
      (by intro b h; cases h)
    intro n hn
    have hm := midpointFour_mesh hn
    refine ⟨rfl,by norm_num [midpointFour],?_,le_rfl,hm.1,?_,midpointFour_cost hn⟩
    · dsimp [midpointFour]; positivity
    · rw [hm.2]; nlinarith [sq_nonneg (midpointFour n).tilt]
  · apply real_row .midpoint (η := 1/1000) (by norm_num) (by norm_num)
      (by intro b h; cases h)
    intro t ht
    have hm := midpointOne_mesh ht
    refine ⟨rfl,by norm_num [midpointOne],ht,le_rfl,hm.1,?_,midpointOne_cost t⟩
    exact hm.2.trans (by nlinarith [sq_nonneg (midpointOne t).tilt])
  · apply integer_row .midpoint (η := 1/1000) (by norm_num) (by norm_num)
      (by intro b h; cases h)
    intro n hn
    have hm := midpointTwo_mesh hn
    refine ⟨rfl,by norm_num [midpointTwo],?_,?_,hm.1,?_,midpointTwo_cost hn⟩
    · dsimp [midpointTwo]; positivity
    · exact div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) (by positivity)
    · rw [hm.2]; nlinarith [sq_nonneg (midpointTwo n).tilt]
  · obtain ⟨δ,A,hδ,hA,hr⟩ := uniform_rows .radial (η := 1/1000)
      (by norm_num) (by norm_num) (by intro b h; cases h)
    refine ⟨δ,A,hδ,hA,?_⟩
    intro c hc hcδ m hcm
    have hm := continuousTwo_mesh hc hcm
    apply hr (continuousTwo c m) rfl (by norm_num [continuousTwo]) hc hcδ hm.1
      (hm.2.trans (by nlinarith [sq_nonneg (continuousTwo c m).tilt])) _ c hc.le
      (by dsimp [continuousTwo]; linarith) (continuousTwo_cost c m)
  · apply integer_row .squared (η := 1/960) (by norm_num) (by norm_num)
      (by intro b h; cases h)
    intro n hn
    have hm := squaredTwo_mesh hn
    refine ⟨rfl,by norm_num [squaredTwo],?_,le_rfl,hm.1,?_,squaredTwo_cost hn⟩
    · dsimp [squaredTwo]; positivity
    · rw [hm.2]; nlinarith [sq_nonneg (squaredTwo n).tilt]
  · apply integer_row .maximum (η := 1/960) (by norm_num) (by norm_num)
      (by intro b h; cases h)
    intro n hn
    have hm := maximumOne_mesh hn
    refine ⟨rfl,by norm_num [maximumOne],?_,?_,hm.1,hm.2.le,maximumOne_cost hn⟩
    · dsimp [maximumOne]; positivity
    · change 1/(4*(n:ℝ)) ≤ 2/(n:ℝ)
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [show (0:ℝ) ≤ n by positivity]
  · apply real_row (.cartesian (3/4)) (η := 1/960) (by norm_num) (by norm_num)
      (by intro b h; cases h; norm_num)
    intro t ht
    have hm := cartesianThreeQuarters_mesh ht
    refine ⟨rfl,by dsimp [cartesianThreeQuarters]; positivity,?_,?_,hm.1,?_,
      cartesianThreeQuarters_cost t⟩
    · dsimp [cartesianThreeQuarters]; positivity
    · dsimp [cartesianThreeQuarters]; linarith
    · exact hm.2.trans (by nlinarith [sq_nonneg (cartesianThreeQuarters t).tilt])
  · apply integer_row (.cartesian 1) (η := 1/1000) (by norm_num) (by norm_num)
      (by intro b h; cases h; norm_num)
    intro n hn
    have hm := cartesianOne_mesh hn
    refine ⟨rfl,by norm_num [cartesianOne],?_,?_,hm.1,?_,cartesianOne_cost hn⟩
    · dsimp [cartesianOne]; positivity
    · change 1/(2*(n:ℝ)) ≤ 2/(n:ℝ)
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [show (0:ℝ) ≤ n by positivity]
    · rw [hm.2]; nlinarith [sq_nonneg (cartesianOne n).tilt]

end CylinderCovering.AngularTableCover

end

end OAI
