import OAI.Dynamics.StandardMap.ShapeComponents

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
def slowCore (d : ℝ → ℝ → ℝ) : Set ℝ := (locallyUnitSet d)ᶜ
lemma isClosed_slowCore (d : ℝ → ℝ → ℝ) : IsClosed (slowCore d) := (isOpen_locallyUnitSet d).isClosed_compl
lemma unit_Iic_local {d : ℝ → ℝ → ℝ} {a x : ℝ} (h : ∀s≤ a,∀t≤ a,d s t=|t-s|) (hx : x< a) :
    LocallyAffineAt d x 1 := by
  refine ⟨(a-x)/2,by linarith,?_⟩
  intro s hs t ht
  rw [mem_ball,Real.dist_eq,abs_lt] at hs ht
  simpa only [one_mul] using h s (by linarith [hs.2]) t (by linarith [ht.2])
lemma unit_Ici_local {d : ℝ → ℝ → ℝ} {a x : ℝ} (h : ∀s≥a,∀t≥a,d s t=|t-s|) (hx : a< x) :
    LocallyAffineAt d x 1 := by
  refine ⟨(x-a)/2,by linarith,?_⟩
  intro s hs t ht
  rw [mem_ball,Real.dist_eq,abs_lt] at hs ht
  simpa only [one_mul] using h s (by linarith [hs.1]) t (by linarith [ht.1])
lemma nonaffine_has_nonlocal {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (hn : NonaffineLine d) :
    ∃x:ℝ,¬∃w,LocallyAffineAt d x w := by
  by_contra h
  push Not at h
  have hh : ∀x∈(univ:Set ℝ),∃w,LocallyAffineAt d x w := fun x _ => h x
  obtain ⟨w,_,_,_,ha⟩ := connected_affine_full hd univ isPreconnected_univ ⟨0,mem_univ _⟩ hh
  exact hn ⟨w,fun x y => ha x (mem_univ _) y (mem_univ _)⟩
lemma slowCore_nonempty {d : ℝ → ℝ → ℝ} (hd : TreeLine d) (hn : NonaffineLine d) : (slowCore d).Nonempty := by
  obtain ⟨x,hx⟩ := nonaffine_has_nonlocal hd hn
  exact ⟨x,fun h => hx ⟨1,h⟩⟩
lemma slowCore_ordConnected {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c : ℝ}
    (hp : SlowPair d c) (hc1 : c<1) : OrdConnected (slowCore d) := by
  constructor
  intro x hx y hy z hz
  by_contra hz'
  have hzu : LocallyAffineAt d z 1 := not_not.mp hz'
  rcases fast_local_ray hd hc hn hp hc1 hzu hc1 with ⟨a,hza,_,ha⟩|⟨a,haz,_,ha⟩
  · exact hx (unit_Iic_local ha (lt_of_le_of_lt hz.1 hza))
  · exact hy (unit_Ici_local ha (lt_of_lt_of_le haz hz.2))
lemma slowCore_local_speed {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c x w : ℝ}
    (hp : SlowPair d c) (hx : x∈slowCore d) (hw : LocallyAffineAt d x w) : w≤ c := by
  by_contra hh
  have he := fast_component_speed_one hd hc hn hp hw (lt_of_not_ge hh)
  rw [he] at hw
  exact hx hw
lemma slow_affine_prefix {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c a b : ℝ}
    (hp : SlowPair d c) (hab : a< b) (ha : a∈slowCore d)
    (hlocal : ∀x∈Ico a b,∃w,LocallyAffineAt d x w) : d a b≤ c*(b-a) := by
  obtain ⟨w,_,_,hl,he⟩ := connected_affine_full hd (Ico a b) isPreconnected_Ico ⟨a,⟨le_rfl,hab⟩⟩ hlocal
  have hw := slowCore_local_speed hd hc hn hp ha (hl a ⟨le_rfl,hab⟩)
  have hcl := affineOn_closure hc (Ico a b) w he
  rw [closure_Ico hab.ne] at hcl
  have heq := hcl a ⟨le_rfl,hab.le⟩ b ⟨hab.le,le_rfl⟩
  rw [abs_of_pos (sub_pos.mpr hab)] at heq
  rw [heq]
  exact mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr hab.le)
lemma slow_affine_suffix {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c a b : ℝ}
    (hp : SlowPair d c) (hab : a< b) (hb : b∈slowCore d)
    (hlocal : ∀x∈Ioc a b,∃w,LocallyAffineAt d x w) : d a b≤ c*(b-a) := by
  obtain ⟨w,_,_,hl,he⟩ := connected_affine_full hd (Ioc a b) isPreconnected_Ioc ⟨b,⟨hab,le_rfl⟩⟩ hlocal
  have hw := slowCore_local_speed hd hc hn hp hb (hl b ⟨hab,le_rfl⟩)
  have hcl := affineOn_closure hc (Ioc a b) w he
  rw [closure_Ioc hab.ne] at hcl
  have heq := hcl a ⟨le_rfl,hab.le⟩ b ⟨hab.le,le_rfl⟩
  rw [abs_of_pos (sub_pos.mpr hab)] at heq
  rw [heq]
  exact mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr hab.le)
lemma slowCore_secant_sorted {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c x y : ℝ}
    (hp : SlowPair d c) (hxy : x< y) (hx : x∈slowCore d) (hy : y∈slowCore d) :
    d x y≤ c*(y-x) := by
  let C : Set ℝ := Icc x y ∩ (locallyAffineSet d)ᶜ
  have hC : IsCompact C := isCompact_Icc.inter_right (isOpen_locallyAffineSet d).isClosed_compl
  by_cases hne : C.Nonempty
  · let p := sInf C
    let q := sSup C
    have hpC : p∈C := hC.sInf_mem hne
    have hqC : q∈C := hC.sSup_mem hne
    have hxp : x≤ p := hpC.1.1
    have hqy : q≤ y := hqC.1.2
    have hpq : p≤ q := csInf_le hC.bddBelow hqC
    have hleft : d x p≤ c*(p-x) := by
      rcases lt_or_eq_of_le hxp with h|h
      · apply slow_affine_prefix hd hc hn hp h hx
        intro z hz
        by_contra hz'
        have hzC : z∈C := ⟨⟨hz.1,hz.2.le.trans hpC.1.2⟩,hz'⟩
        have hmin := csInf_le hC.bddBelow hzC
        change p≤ z at hmin
        linarith [hz.2]
      · rw [←h]; simp only [hd.self,sub_self,mul_zero,le_refl]
    have hright : d q y≤ c*(y-q) := by
      rcases lt_or_eq_of_le hqy with h|h
      · apply slow_affine_suffix hd hc hn hp h hy
        intro z hz
        by_contra hz'
        have hzC : z∈C := ⟨⟨hqC.1.1.trans hz.1.le,hz.2⟩,hz'⟩
        have hmax := le_csSup hC.bddAbove hzC
        change z≤ q at hmax
        linarith [hz.1]
      · rw [h]; simp only [hd.self,sub_self,mul_zero,le_refl]
    have hmid := hp p q hpC.2 (fun h => hqC.2 ⟨1,h⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hpq)] at hmid
    have h1 := hd.triangle x p y
    have h2 := hd.triangle p q y
    nlinarith
  · have hlocal : ∀z∈Icc x y,∃w,LocallyAffineAt d z w := by
      intro z hz
      by_contra hh
      exact hne ⟨z,hz,hh⟩
    obtain ⟨w,_,_,hl,he⟩ := connected_affine_full hd (Icc x y) isPreconnected_Icc ⟨x,⟨le_rfl,hxy.le⟩⟩ hlocal
    have hw := slowCore_local_speed hd hc hn hp hx (hl x ⟨le_rfl,hxy.le⟩)
    rw [he x ⟨le_rfl,hxy.le⟩ y ⟨hxy.le,le_rfl⟩,abs_of_pos (sub_pos.mpr hxy)]
    exact mul_le_mul_of_nonneg_right hw (sub_nonneg.mpr hxy.le)
lemma slowCore_secant {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (Function.uncurry d)) (hn : NonaffineLine d) {c x y : ℝ}
    (hp : SlowPair d c) (hx : x∈slowCore d) (hy : y∈slowCore d) : d x y≤ c*|y-x| := by
  rcases lt_trichotomy x y with h|rfl|h
  · rw [abs_of_pos (sub_pos.mpr h)]; exact slowCore_secant_sorted hd hc hn hp h hx hy
  · simp only [hd.self,sub_self,abs_zero,mul_zero,le_refl]
  · rw [hd.symm,abs_sub_comm,abs_of_pos (sub_pos.mpr h)]; exact slowCore_secant_sorted hd hc hn hp h hy hx
end StandardMapEntropy

end OAI
