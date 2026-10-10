import Mathlib
import OAI.Geometry.Cannon.Energy.Square

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonChart

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def liftPath (e : X → Y) (he : IsEmbedding e) {a b : X}
    (p : Path (e a) (e b)) (hp : ∀ t, p t ∈ range e) : Path a b where
  toFun := fun t => he.toHomeomorph.symm ⟨p t,hp t⟩
  continuous_toFun := he.toHomeomorph.symm.continuous.comp (p.continuous.subtype_mk hp)
  source' := by
    apply he.toHomeomorph.injective
    simp
  target' := by
    apply he.toHomeomorph.injective
    simp

lemma liftPath_apply (e : X → Y) (he : IsEmbedding e) {a b : X}
    (p : Path (e a) (e b)) (hp : ∀ t, p t ∈ range e) (t : unitInterval) :
    e (liftPath e he p hp t) = p t := by
  have hh := he.toHomeomorph.apply_symm_apply ⟨p t,hp t⟩
  exact congrArg Subtype.val hh

lemma lift_joinedIn (e : X → Y) (he : IsEmbedding e) {a b : X} {S : Set Y}
    (hS : S ⊆ range e) (hp : JoinedIn S (e a) (e b)) :
    JoinedIn (e ⁻¹' S) a b := by
  obtain ⟨p,hp⟩ := hp
  let hpr : ∀ t, p t ∈ range e := fun t => hS (hp t)
  refine ⟨liftPath e he p hpr,fun t => ?_⟩
  change e (liftPath e he p hpr t) ∈ S
  rw [liftPath_apply e he p hpr]
  exact hp t

end CannonChart

namespace CannonLevel

open CannonPlanar CannonRegularization

instance : PathConnectedSpace Square :=
  pathConnectedSpace_iff_connectedSpace.mpr inferInstance

theorem regularized_values {f : Square → ℝ} {A B : Set Square}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    (hAf : ∀ z ∈ A, f z = 0) (hBf : ∀ z ∈ B, f z = 1) :
    (∀ z, drain (flood f A) B z ∈ Icc (0 : ℝ) 1) ∧
    (∀ z ∈ A, drain (flood f A) B z = 0) ∧
    (∀ z ∈ B, drain (flood f A) B z = 1) := by
  have hF0 : ∀ z, 0 ≤ flood f A z := fun z => (hf0 z).trans (le_flood hA hf1 z)
  have hF1 := flood_le_upper hA hf1
  have hH0 := drain_lower hB hF0
  have hHF := drain_le hB hF0
  refine ⟨fun z => ⟨hH0 z, (hHF z).trans (hF1 z)⟩, ?_, ?_⟩
  · intro z hz
    apply le_antisymm _ (hH0 z)
    simpa [flood_eq_on_band hA hf1 hz, hAf z hz] using hHF z
  · intro z hz
    rw [drain_eq_on_band hB hF0 hz]
    apply le_antisymm (hF1 z)
    simpa [hBf z hz] using le_flood hA hf1 z

theorem separating_level {f : Square → ℝ} {A B : Set Square}
    (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAedge : ∀ s, (s,0) ∈ A) (hBedge : ∀ s, (s,1) ∈ B)
    (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    (hAf : ∀ z ∈ A, f z = 0) (hBf : ∀ z ∈ B, f z = 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    let H := drain (flood f A) B
    ∃ C : Set Square, IsCompact C ∧ IsConnected C ∧
      (∀ z ∈ C, H z = t) ∧ (∃ z ∈ C, z.1 = 0) ∧ (∃ z ∈ C, z.1 = 1) ∧
      (∀ {x y : Square} (p : Path x y), H x < t → t < H y →
        ∃ s, p s ∈ C) := by
  let F := flood f A
  let H := drain F B
  have hF0 : ∀ z, 0 ≤ F z := fun z => (hf0 z).trans (le_flood hA.nonempty hf1 z)
  have hFc : Continuous F := continuous_flood hA.nonempty hf hf1
  have hHc : Continuous H := continuous_drain hB.nonempty hFc hF0
  obtain ⟨hHr,hHA,hHB⟩ := regularized_values hA.nonempty hB.nonempty hf0 hf1 hAf hBf
  obtain ⟨C,hCc,hCn,hCH,⟨a,ha,ha0⟩,⟨b,hb,hb1⟩⟩ := level_continuum hHc
    (c := t) (fun s => by rw [show H (s,0) = 0 from hHA _ (hAedge s)]; exact ht0.le)
    (fun s => by rw [show H (s,1) = 1 from hHB _ (hBedge s)]; exact ht1.le)
  refine ⟨C,hCc,hCn,hCH,⟨a,ha,ha0⟩,⟨b,hb,hb1⟩,?_⟩
  intro x y p hx hy
  obtain ⟨u,hu,lo,hlo⟩ := regularized_low_side hA.nonempty hB.nonempty hf hf0 hf1 hAf ht0 hx
  obtain ⟨v,hv,hi,hhi⟩ := drain_strict_side hB.nonempty hF0 hy
  obtain ⟨qa,hqa⟩ := hA.joinedIn u hu (0,0) (hAedge 0)
  obtain ⟨qb,hqb⟩ := hB.joinedIn v hv (0,1) (hBedge 0)
  let low : Path x (0,0) := lo.trans qa
  let high : Path y (0,1) := hi.trans qb
  have hlow : ∀ s, H (low s) < t := by
    intro s
    have hs : low s ∈ range lo ∪ range qa := by rw [← Path.trans_range]; exact mem_range_self s
    rcases hs with ⟨r,hr⟩ | ⟨r,hr⟩
    · rw [← hr]; exact hlo r
    · rw [← hr, show H (qa r) = 0 from hHA _ (hqa r)]; exact ht0
  have hhigh : ∀ s, t < H (high s) := by
    intro s
    have hs : high s ∈ range hi ∪ range qb := by rw [← Path.trans_range]; exact mem_range_self s
    rcases hs with ⟨r,hr⟩ | ⟨r,hr⟩
    · rw [← hr]; exact hhi r
    · rw [← hr, show H (qb r) = 1 from hHB _ (hqb r)]; exact ht1
  let q := high.symm.trans (p.symm.trans low)
  obtain ⟨s,hs⟩ := continuum_crosses_path hCn.isPreconnected ha hb ha0 hb1 q.continuous
    (by simp [q]) (by simp [q])
  have hqs : q s ∈ range high.symm ∪ (range p.symm ∪ range low) := by
    rw [← Path.trans_range, ← Path.trans_range]
    exact mem_range_self s
  rcases hqs with ⟨r,hr⟩ | ⟨r,hr⟩ | ⟨r,hr⟩
  · have ht := hhigh (unitInterval.symm r)
    have he := hCH _ hs
    change H (high.symm r) > t at ht
    rw [hr,he] at ht
    exact False.elim (lt_irrefl _ ht)
  · exact ⟨unitInterval.symm r, hr.symm ▸ hs⟩
  · have ht := hlow r
    rw [hr,hCH _ hs] at ht
    exact False.elim (lt_irrefl _ ht)

lemma slab_pathConnected {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IsPathConnected {z : Square | a ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ b} := by
  let e : Square → ℝ × ℝ := Prod.map Subtype.val Subtype.val
  have he : Topology.IsInducing e := Topology.IsInducing.subtypeVal.prodMap
    Topology.IsInducing.subtypeVal
  rw [he.isPathConnected_iff]
  have himage : e '' {z : Square | a ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ b} =
      Icc ((0 : ℝ),a) (1,b) := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨⟨w.1.property.1,hw.1⟩,⟨w.1.property.2,hw.2⟩⟩
    · intro hz
      refine ⟨(⟨z.1,hz.1.1,hz.2.1⟩,⟨z.2,ha.trans hz.1.2,hz.2.2.trans hb⟩), ?_, rfl⟩
      exact ⟨hz.1.2,hz.2.2⟩
  rw [himage]
  exact (convex_Icc _ _).isPathConnected ⟨(0,a),⟨le_rfl,⟨zero_le_one,hab⟩⟩⟩

def topBand : Set Square := {z | (z.2 : ℝ) ≤ 1 / 3}

def bottomBand : Set Square := {z | 2 / 3 ≤ (z.2 : ℝ)}

def centralRectangle : Set Square := {z | (z.2 : ℝ) ∈ Icc (1 / 3) (2 / 3)}

lemma topBand_pathConnected : IsPathConnected topBand := by
  convert slab_pathConnected (a := 0) (b := 1 / 3) (by norm_num) (by norm_num) (by norm_num) using 1
  ext z
  exact ⟨fun hz => ⟨z.2.property.1,hz⟩,fun hz => hz.2⟩

lemma bottomBand_pathConnected : IsPathConnected bottomBand := by
  convert slab_pathConnected (a := 2 / 3) (b := 1) (by norm_num) (by norm_num) (by norm_num) using 1
  ext z
  exact ⟨fun hz => ⟨hz,z.2.property.2⟩,fun hz => hz.1⟩

theorem rectangle_separating_level {f : Square → ℝ}
    (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    (hAf : ∀ z ∈ topBand, f z = 0) (hBf : ∀ z ∈ bottomBand, f z = 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    let H := drain (flood f topBand) bottomBand
    ∃ C : Set Square, IsCompact C ∧ IsConnected C ∧ C ⊆ centralRectangle ∧
      (∀ z ∈ C, H z = t) ∧ (∃ z ∈ C, z.1 = 0) ∧ (∃ z ∈ C, z.1 = 1) ∧
      (∀ {x y : Square} (p : Path x y), H x < t → t < H y → ∃ s, p s ∈ C) := by
  obtain ⟨C,hCc,hCn,hCH,hCl,hCr,hCs⟩ := separating_level topBand_pathConnected bottomBand_pathConnected
    (by intro s; change (0 : ℝ) ≤ 1 / 3; norm_num)
    (by intro s; change (2 : ℝ) / 3 ≤ 1; norm_num)
    hf hf0 hf1 hAf hBf ht0 ht1
  refine ⟨C,hCc,hCn,?_,hCH,hCl,hCr,hCs⟩
  obtain ⟨_,hHA,hHB⟩ := regularized_values topBand_pathConnected.nonempty
    bottomBand_pathConnected.nonempty hf0 hf1 hAf hBf
  intro z hz
  constructor
  · by_contra h
    have he := hHA z (show z ∈ topBand from (lt_of_not_ge h).le)
    rw [hCH z hz] at he
    exact (ne_of_gt ht0) he
  · by_contra h
    have he := hHB z (show z ∈ bottomBand from (lt_of_not_ge h).le)
    rw [hCH z hz] at he
    exact (ne_of_lt ht1) he

end CannonLevel

end
end
end
end
end
end
end
end
end

end OAI
