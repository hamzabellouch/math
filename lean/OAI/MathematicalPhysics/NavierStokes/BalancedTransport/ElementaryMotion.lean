import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Deformation

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

def RationalConstant (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.RationalConstant
open BalancedTransport.Geometry Set

lemma rat (q : ℚ) : RationalConstant (q : ℝ) := ⟨q,rfl⟩

lemma nat (n : ℕ) : RationalConstant (n : ℝ) := ⟨n, by simp⟩

lemma zero : RationalConstant 0 := by simpa using rat 0

lemma one : RationalConstant 1 := by simpa using rat 1

lemma add {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) : RationalConstant (a+b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a+b, by simp⟩

lemma sub {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) : RationalConstant (a-b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a-b, by simp⟩

lemma mul {a b : ℝ} (ha : RationalConstant a) (hb : RationalConstant b) : RationalConstant (a*b) := by
  obtain ⟨a,rfl⟩ := ha; obtain ⟨b,rfl⟩ := hb
  exact ⟨a*b, by simp⟩

lemma elementary {d : ℕ} [NeZero d] {a : ℝ} (ha : RationalConstant a) :
    Elementary (fun _ : Fin d → ℝ => a) := by
  obtain ⟨a,rfl⟩ := ha; exact Elementary.literal a

end BalancedTransport.Effectivity.RationalConstant
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set

def RationalCenters {ι : Type*} (a : ι → Space) : Prop := ∀ i k, RationalConstant (a i k)

def RationalLayout {ι : Type*} (A : BoxLayout ι) : Prop := RationalCenters A.center ∧ RationalCenters A.width

def ElementaryCurve (f : ℝ → ℝ) : Prop := Elementary (fun x : Fin 1 → ℝ => f (x 0))

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry Set

lemma const {c : ℝ} (hc : RationalConstant c) : ElementaryCurve (fun _ => c) := hc.elementary

lemma id : ElementaryCurve (fun t => t) := Elementary.coordinate 0

lemma add {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f t + g t) := Elementary.add hf hg

lemma sub {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f t - g t) := Elementary.sub hf hg

lemma mul {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f t * g t) := Elementary.mul hf hg

lemma div_const {f : ℝ → ℝ} (hf : ElementaryCurve f) {c : ℝ} (hc : RationalConstant c) :
    ElementaryCurve (fun t => f t / c) := by
  obtain ⟨c,rfl⟩ := hc; exact hf.div_rat c

lemma exp {f : ℝ → ℝ} (hf : ElementaryCurve f) : ElementaryCurve (fun t => Real.exp (f t)) := Elementary.exp hf

lemma comp {f g : ℝ → ℝ} (hf : ElementaryCurve f) (hg : ElementaryCurve g) :
    ElementaryCurve (fun t => f (g t)) := Elementary.comp hf (fun x _ => g (x 0)) (fun _ => hg)

lemma transition : ElementaryCurve Real.smoothTransition := id.smoothTransition

lemma log {c : ℝ} (hc : RationalConstant c) (hp : 0 < c) : ElementaryCurve (fun _ => Real.log c) := by
  obtain ⟨c,rfl⟩ := hc
  exact Elementary.log_rat (by exact_mod_cast hp)

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

def ElementaryMotion {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}
    (m : BoxMotion A B safe η) : Prop :=
  (∀ i k, ElementaryCurve (fun t => m.center t i k)) ∧
  (∀ i k, ElementaryCurve (fun t => m.width t i k))

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryMotion
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]
variable {A B C : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma stationary (hA : RationalLayout A) (hp : A.Positive) (hs : A.Separated η)
    (hg : A.Guarded safe) : ElementaryMotion (BoxMotion.stationary hp hs hg) :=
  ⟨fun i k => ElementaryCurve.const (hA.1 i k), fun i k => ElementaryCurve.const (hA.2 i k)⟩

lemma trans {m : BoxMotion A B safe η} {n : BoxMotion B C safe η}
    (hm : ElementaryMotion m) (hn : ElementaryMotion n) (hB : RationalLayout B) :
    ElementaryMotion (m.trans n) := by
  have h₂ : ElementaryCurve (fun t => 2*t) :=
    (ElementaryCurve.const (RationalConstant.nat 2)).mul ElementaryCurve.id
  have h₂' : ElementaryCurve (fun t => 2*t-1) := h₂.sub (ElementaryCurve.const RationalConstant.one)
  constructor <;> intro i k
  · exact ((hm.1 i k).comp h₂).add ((hn.1 i k).comp h₂') |>.sub (ElementaryCurve.const (hB.1 i k))
  · exact (((hm.2 i k).comp h₂).mul ((hn.2 i k).comp h₂')).div_const (hB.2 i k)

lemma reverse {m : BoxMotion A B safe η} (hm : ElementaryMotion m) : ElementaryMotion m.reverse := by
  have h : ElementaryCurve (fun t => 1-t) :=
    (ElementaryCurve.const RationalConstant.one).sub ElementaryCurve.id
  exact ⟨fun i k => (hm.1 i k).comp h, fun i k => (hm.2 i k).comp h⟩

lemma segment {a b w : ι → Space} (ha : RationalCenters a) (hb : RationalCenters b)
    (hw : RationalCenters w) (hp : ∀ i k, 0 < w i k)
    (hs : ∀ r ∈ Icc (0 : ℝ) 1, (segmentLayout a b w r).Separated η)
    (hg : ∀ r ∈ Icc (0 : ℝ) 1, (segmentLayout a b w r).Guarded safe) :
    ElementaryMotion (segmentMotion hp hs hg) := by
  refine ⟨?_, fun i k => ElementaryCurve.const (hw i k)⟩
  intro i k
  exact (((ElementaryCurve.const RationalConstant.one).sub ElementaryCurve.transition).mul
    (ElementaryCurve.const (ha i k))).add
    (ElementaryCurve.transition.mul (ElementaryCurve.const (hb i k)))

lemma expansion {a w : ι → Space} {Λ : ℝ} (ha : RationalCenters a)
    (hw : RationalCenters w) (hΛr : RationalConstant Λ)
    (hp : ∀ i k, 0 < w i k) (hs : (BoxLayout.mk a w).Separated η)
    (hg : (BoxLayout.mk a w).Guarded safe) (hΛ : 1 ≤ Λ) :
    ElementaryMotion (expandCenters hp hs hg hΛ) :=
  segment ha (fun i k => hΛr.mul (ha i k)) hw _ _ _

lemma reshape {a h k : ι → Space} {R D : ℝ}
    (ha : RationalCenters a) (hr : RationalCenters h) (kr : RationalCenters k)
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hR : ∀ i j, h i j ≤ R) (kR : ∀ i j, k i j ≤ R)
    (he : ∀ i, ∏ j, h i j = ∏ j, k i j)
    (hD : 2 * R + 4 * η ≤ D) (hs : CenterSeparated a D)
    (hg : ∀ i ∈ safe, 2 + R < a i 0) :
    ElementaryMotion (reshapeMotion hh hk hR kR he hD hs hg) := by
  refine ⟨fun i j => ElementaryCurve.const (ha i j), ?_⟩
  intro i j
  exact ((((ElementaryCurve.const RationalConstant.one).sub ElementaryCurve.transition).mul
    (ElementaryCurve.log (hr i j) (hh i j))).add
    (ElementaryCurve.transition.mul (ElementaryCurve.log (kr i j) (hk i j)))).exp

end BalancedTransport.Effectivity.ElementaryMotion
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma RationalCenters.update [DecidableEq ι] {a : ι → Space} (ha : RationalCenters a)
    (i : ι) {b : Space} (hb : ∀ k, RationalConstant (b k)) : RationalCenters (Function.update a i b) := by
  intro j k
  by_cases h : j = i
  · subst j; simpa using hb k
  · simpa [Function.update_of_ne h] using ha j k

lemma rational_space_update {a : Space} (ha : ∀ k, RationalConstant (a k))
    (j : Fin 3) {b : ℝ} (hb : RationalConstant b) : ∀ k, RationalConstant ((Function.update a j b) k) := by
  intro k
  by_cases he : k = j
  · subst k; simpa using hb
  · simpa [Function.update_of_ne he] using ha k

omit [Fintype ι] in
lemma rational_remaining [DecidableEq ι] {a p : ι → Space} (ha : RationalCenters a)
    (hp : RationalCenters p) (S : Finset ι) : RationalCenters (remainingCenters a p S) := by
  intro i k
  by_cases hi : i ∈ S
  · simpa [remainingCenters, hi] using ha i k
  · simpa [remainingCenters, hi] using hp i k

lemma elementary_singleSegment [DecidableEq ι] {a w : ι → Space} {D η : ℝ} {safe : Set ι}
    (ar : RationalCenters a) (wr : RationalCenters w)
    (i : ι) (b : Space) (br : ∀ k, RationalConstant (b k))
    (hp : ∀ j k, 0 < w j k) (hw : ∀ j l k, w j k + w l k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hb : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i → ∃ k, D < |(1-r)*a i k+r*b k-a j k|)
    (hga : (BoxLayout.mk a w).Guarded safe)
    (hgb : (BoxLayout.mk (Function.update a i b) w).Guarded safe) :
    ElementaryMotion (singleSegmentMotion i b hp hw ha hb hga hgb) :=
  ElementaryMotion.segment ar (ar.update i br) wr _ _ _

end BalancedTransport.Effectivity
end

end OAI
