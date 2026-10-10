import OAI.Geometry.Symplectic.MorseBounds.SphereSmooth

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.CapProduct
open MorseArnold.SphereCaps
open scoped Manifold ContDiff
open Set
noncomputable section
abbrev PlaneFour := (Plane × Plane) × (Plane × Plane)
abbrev SphereFour := (S2 × S2) × (S2 × S2)
abbrev Choices := (Bool × Bool) × (Bool × Bool)
abbrev SP := ((𝓡 2).prod (𝓡 2)).prod ((𝓡 2).prod (𝓡 2))
abbrev PP := (𝓘(ℝ, Plane).prod 𝓘(ℝ, Plane)).prod
  (𝓘(ℝ, Plane).prod 𝓘(ℝ, Plane))
def disk : Set Plane := {z | radiusSq z < 16}
lemma disk_open : IsOpen disk :=
  isOpen_lt ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const

def bigChart (l : ℝ) (hl : 0 < l) (b : Bool) : OpenPartialHomeomorph S2 Plane :=
  if b then southChart l hl else northChart l hl

def oneChart (l : ℝ) (hl : 0 < l) (b : Bool) : OpenPartialHomeomorph S2 Plane :=
  (((bigChart l hl b).symm).restrOpen disk disk_open).symm

def fourChart (l : ℝ) (hl : 0 < l) (nu : Choices) :
    OpenPartialHomeomorph SphereFour PlaneFour :=
  ((oneChart l hl nu.1.1).prod (oneChart l hl nu.1.2)).prod
    ((oneChart l hl nu.2.1).prod (oneChart l hl nu.2.2))

def box : Set PlaneFour := (disk ×ˢ disk) ×ˢ (disk ×ˢ disk)
def fourFlow (l eps t : ℝ) (p : SphereFour) : SphereFour :=
  ((sphereFlow l eps (-1) t p.1.1, sphereFlow l eps (-1) t p.1.2),
    (sphereFlow l eps 1 t p.2.1, sphereFlow l eps 1 t p.2.2))
def quadFlow (t : ℝ) (z : PlaneFour) : PlaneFour :=
  ((rotatePlane t z.1.1, rotatePlane t z.1.2),
    (rotatePlane (-t) z.2.1, rotatePlane (-t) z.2.2))

lemma bigChart_target (l : ℝ) (hl : 0 < l) (b : Bool) :
    (bigChart l hl b).target = {z | radiusSq z < 4 * l} := by
  cases b <;> rfl

lemma oneChart_source (l : ℝ) (hl : 0 < l) (b : Bool) :
    (oneChart l hl b).source = (bigChart l hl b).source ∩ (bigChart l hl b) ⁻¹' disk := rfl

lemma oneChart_target (l : ℝ) (hl : 25 / 2 < l) (b : Bool) :
    (oneChart l (by linarith) b).target = disk := by
  change (bigChart l _ b).target ∩ disk = disk
  rw [bigChart_target]
  apply inter_eq_right.mpr
  intro z hz
  change radiusSq z < 16 at hz
  change radiusSq z < 4 * l
  linarith

theorem four_chart_target (l : ℝ) (hl : 25 / 2 < l) (nu : Choices) :
    (fourChart l (by linarith) nu).target = box := by
  change (((oneChart l _ nu.1.1).target ×ˢ (oneChart l _ nu.1.2).target) ×ˢ
    ((oneChart l _ nu.2.1).target ×ˢ (oneChart l _ nu.2.2).target)) = box
  rw [oneChart_target l hl, oneChart_target l hl,
    oneChart_target l hl, oneChart_target l hl]
  rfl

lemma bigChart_smooth (l : ℝ) (hl : 0 < l) (b : Bool) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, Plane) ∞ (bigChart l hl b) (bigChart l hl b).source ∧
    ContMDiffOn 𝓘(ℝ, Plane) (𝓡 2) ∞ (bigChart l hl b).symm (bigChart l hl b).target := by
  cases b
  · exact ⟨fun p hp => (smooth_north l hl p hp).contMDiffWithinAt,
      fun z hz => (smooth_northInv l hl z hz).contMDiffWithinAt⟩
  · exact ⟨fun p hp => (smooth_south l hl p hp).contMDiffWithinAt,
      fun z hz => ((flipS_smooth.contMDiffAt).comp z
        (smooth_northInv l hl z hz)).contMDiffWithinAt⟩

lemma oneChart_smooth (l : ℝ) (hl : 0 < l) (b : Bool) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, Plane) ∞ (oneChart l hl b) (oneChart l hl b).source ∧
    ContMDiffOn 𝓘(ℝ, Plane) (𝓡 2) ∞ (oneChart l hl b).symm (oneChart l hl b).target := by
  exact ⟨(bigChart_smooth l hl b).1.mono inter_subset_left,
    (bigChart_smooth l hl b).2.mono inter_subset_left⟩

theorem four_chart_smooth (l : ℝ) (hl : 25 / 2 < l) (nu : Choices) :
    ContMDiffOn SP PP ∞ (fourChart l (by linarith) nu)
      (fourChart l (by linarith) nu).source ∧
    ContMDiffOn PP SP ∞ (fourChart l (by linarith) nu).symm box := by
  have hpos : 0 < l := by linarith
  constructor
  · exact (((oneChart_smooth l hpos nu.1.1).1).prodMap
      ((oneChart_smooth l hpos nu.1.2).1)).prodMap
      (((oneChart_smooth l hpos nu.2.1).1).prodMap
      ((oneChart_smooth l hpos nu.2.2).1))
  · rw [← four_chart_target l hl nu]
    exact (((oneChart_smooth l hpos nu.1.1).2).prodMap
      ((oneChart_smooth l hpos nu.1.2).2)).prodMap
      (((oneChart_smooth l hpos nu.2.1).2).prodMap
      ((oneChart_smooth l hpos nu.2.2).2))

lemma one_cap_disjoint (l : ℝ) (hl : 25 / 2 < l) :
    Disjoint (oneChart l (by linarith) false).source
      (oneChart l (by linarith) true).source := by
  refine (caps_disjoint l hl).mono ?_ ?_
  · intro p hp
    exact ⟨hp.1, lt_trans hp.2 (by norm_num)⟩
  · intro p hp
    exact ⟨hp.1, lt_trans hp.2 (by norm_num)⟩

lemma one_overlap_eq (l : ℝ) (hl : 25 / 2 < l) (b c : Bool) (p : S2)
    (hb : p ∈ (oneChart l (by linarith) b).source)
    (hc : p ∈ (oneChart l (by linarith) c).source) : b = c := by
  cases b <;> cases c
  · rfl
  · exact ((Set.disjoint_left.mp (one_cap_disjoint l hl)) hb hc).elim
  · exact ((Set.disjoint_left.mp (one_cap_disjoint l hl)) hc hb).elim
  · rfl

theorem four_caps_disjoint (l : ℝ) (hl : 25 / 2 < l) :
    Pairwise (fun nu mu : Choices => Disjoint
      (fourChart l (by linarith) nu).source
      (fourChart l (by linarith) mu).source) := by
  intro nu mu hne
  apply Set.disjoint_left.mpr
  intro p hp hq
  apply hne
  apply Prod.ext <;> apply Prod.ext
  · exact one_overlap_eq l hl _ _ p.1.1 hp.1.1 hq.1.1
  · exact one_overlap_eq l hl _ _ p.1.2 hp.1.2 hq.1.2
  · exact one_overlap_eq l hl _ _ p.2.1 hp.2.1 hq.2.1
  · exact one_overlap_eq l hl _ _ p.2.2 hp.2.2 hq.2.2

lemma one_endpoint (l eps s : ℝ) (hl : 25 / 2 < l) (b : Bool)
    (hs : s = -1 ∨ s = 1) (p : S2) (hp : p ∈ (oneChart l (by linarith) b).source) :
    oneChart l (by linarith) b (sphereFlow l eps s 1 p) =
      rotatePlane (-s * eps) (oneChart l (by linarith) b p) := by
  cases b
  · exact sphereFlow_north_endpoint l eps s hl hs p hp.1 (lt_trans hp.2 (by norm_num))
  · exact sphereFlow_south_endpoint l eps s hl hs p hp.1 (lt_trans hp.2 (by norm_num))

theorem four_endpoint (l eps : ℝ) (hl : 25 / 2 < l) (nu : Choices) :
    ∀ p ∈ (fourChart l (by linarith) nu).source,
      fourChart l (by linarith) nu (fourFlow l eps 1 p) =
        quadFlow eps (fourChart l (by linarith) nu p) := by
  intro p hp
  apply Prod.ext <;> apply Prod.ext
  · simpa [fourChart, fourFlow, quadFlow] using one_endpoint l eps (-1) hl nu.1.1 (Or.inl rfl) p.1.1 hp.1.1
  · simpa [fourChart, fourFlow, quadFlow] using one_endpoint l eps (-1) hl nu.1.2 (Or.inl rfl) p.1.2 hp.1.2
  · simpa [fourChart, fourFlow, quadFlow] using one_endpoint l eps 1 hl nu.2.1 (Or.inr rfl) p.2.1 hp.2.1
  · simpa [fourChart, fourFlow, quadFlow] using one_endpoint l eps 1 hl nu.2.2 (Or.inr rfl) p.2.2 hp.2.2

lemma pole_in_cap (l : ℝ) (hl : 25 / 2 < l) (p : S2) (hp : p ∈ poleSet) :
    ∃ b : Bool, p ∈ (oneChart l (by linarith) b).source := by
  rcases hp with ⟨h0,h1⟩
  have hh : ((p : R3) 2 - 1) * ((p : R3) 2 + 1) = 0 := by
    have h := sphere_equation p
    rw [h0,h1] at h
    nlinarith
  rcases mul_eq_zero.mp hh with h | h
  · have h2 : (p : R3) 2 = 1 := by linarith
    refine ⟨false, ?_⟩
    change -1 < (p : R3) 2 ∧ radiusSq (north l p) < 16
    simp [h2, north, radiusSq, h0, h1]
  · have h2 : (p : R3) 2 = -1 := by linarith
    refine ⟨true, ?_⟩
    change (p : R3) 2 < 1 ∧ radiusSq (south l p) < 16
    simp [h2, south, radiusSq, h0, h1]

theorem exterior_not_fixed (l eps : ℝ) (hl : 25 / 2 < l)
    (heps : 0 < eps) (hepspi : eps < Real.pi) :
    ∀ p : SphereFour, (∀ nu : Choices, p ∉ (fourChart l (by linarith) nu).source) →
      fourFlow l eps 1 p ≠ p := by
  intro p hp he
  have h1 : p.1.1 ∈ poleSet := (sphereFlow_fixed l eps (-1) heps hepspi p.1.1).mp
    (congrArg (fun q : SphereFour => q.1.1) he)
  have h2 : p.1.2 ∈ poleSet := (sphereFlow_fixed l eps (-1) heps hepspi p.1.2).mp
    (congrArg (fun q : SphereFour => q.1.2) he)
  have h3 : p.2.1 ∈ poleSet := (sphereFlow_fixed l eps 1 heps hepspi p.2.1).mp
    (congrArg (fun q : SphereFour => q.2.1) he)
  have h4 : p.2.2 ∈ poleSet := (sphereFlow_fixed l eps 1 heps hepspi p.2.2).mp
    (congrArg (fun q : SphereFour => q.2.2) he)
  obtain ⟨b1,hb1⟩ := pole_in_cap l hl p.1.1 h1
  obtain ⟨b2,hb2⟩ := pole_in_cap l hl p.1.2 h2
  obtain ⟨b3,hb3⟩ := pole_in_cap l hl p.2.1 h3
  obtain ⟨b4,hb4⟩ := pole_in_cap l hl p.2.2 h4
  exact hp ((b1,b2),(b3,b4)) ⟨⟨hb1,hb2⟩,⟨hb3,hb4⟩⟩

lemma one_preserves (l eps s t : ℝ) (hl : 0 < l) (b : Bool) :
    ∀ p ∈ (oneChart l hl b).source,
      sphereFlow l eps s t p ∈ (oneChart l hl b).source := by
  intro p hp
  have hh : (sphereFlow l eps s t p : R3) 2 = (p : R3) 2 := rotate_height _ p
  cases b
  · change -1 < (p : R3) 2 ∧ radiusSq (north l p) < 16 at hp
    change -1 < (sphereFlow l eps s t p : R3) 2 ∧
      radiusSq (north l (sphereFlow l eps s t p)) < 16
    have hh' : -1 < (sphereFlow l eps s t p : R3) 2 := by rw [hh]; exact hp.1
    refine ⟨hh', ?_⟩
    rw [north_radius l hl _ hh', hh, ← north_radius l hl p hp.1]
    exact hp.2
  · change (p : R3) 2 < 1 ∧ radiusSq (south l p) < 16 at hp
    change (sphereFlow l eps s t p : R3) 2 < 1 ∧
      radiusSq (south l (sphereFlow l eps s t p)) < 16
    have hh' : (sphereFlow l eps s t p : R3) 2 < 1 := by rw [hh]; exact hp.1
    refine ⟨hh', ?_⟩
    rw [south_radius l hl _ hh', hh, ← south_radius l hl p hp.1]
    exact hp.2

theorem four_preserves (l eps t : ℝ) (hl : 25 / 2 < l) (nu : Choices) :
    ∀ p ∈ (fourChart l (by linarith) nu).source,
      fourFlow l eps t p ∈ (fourChart l (by linarith) nu).source := by
  intro p hp
  exact ⟨⟨one_preserves l eps (-1) t (by linarith) _ _ hp.1.1,
    one_preserves l eps (-1) t (by linarith) _ _ hp.1.2⟩,
    ⟨one_preserves l eps 1 t (by linarith) _ _ hp.2.1,
    one_preserves l eps 1 t (by linarith) _ _ hp.2.2⟩⟩

lemma smooth_time_pair {V T B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace T] [TopologicalSpace B] (J : ModelWithCorners ℝ V B)
    [ChartedSpace B T] (f g : ℝ × T → T)
    (hf : ContMDiff (𝓘(ℝ).prod J) J ∞ f)
    (hg : ContMDiff (𝓘(ℝ).prod J) J ∞ g) :
    ContMDiff (𝓘(ℝ).prod (J.prod J)) (J.prod J) ∞
      (fun q : ℝ × (T × T) => (f (q.1,q.2.1),g (q.1,q.2.2))) := by
  have h1 : ContMDiff (𝓘(ℝ).prod (J.prod J)) (𝓘(ℝ).prod J) ∞
      (fun q : ℝ × (T × T) => (q.1,q.2.1)) :=
    contMDiff_fst.prodMk contMDiff_snd.fst
  have h2 : ContMDiff (𝓘(ℝ).prod (J.prod J)) (𝓘(ℝ).prod J) ∞
      (fun q : ℝ × (T × T) => (q.1,q.2.2)) :=
    contMDiff_fst.prodMk contMDiff_snd.snd
  exact (hf.comp h1).prodMk (hg.comp h2)

lemma pairFlow_smooth (l eps s : ℝ) :
    ContMDiff (𝓘(ℝ).prod ((𝓡 2).prod (𝓡 2))) ((𝓡 2).prod (𝓡 2)) ∞
      (fun q : ℝ × (S2 × S2) =>
        (sphereFlow l eps s q.1 q.2.1, sphereFlow l eps s q.1 q.2.2)) :=
  smooth_time_pair (𝓡 2) _ _ (sphereFlow_smooth l eps s) (sphereFlow_smooth l eps s)

theorem four_flow_smooth (l eps : ℝ) :
    ContMDiff (𝓘(ℝ).prod SP) SP ∞ (fun q : ℝ × SphereFour => fourFlow l eps q.1 q.2) :=
  smooth_time_pair ((𝓡 2).prod (𝓡 2)) _ _ (pairFlow_smooth l eps (-1)) (pairFlow_smooth l eps 1)

end
end MorseArnold.CapProduct

end

end OAI
