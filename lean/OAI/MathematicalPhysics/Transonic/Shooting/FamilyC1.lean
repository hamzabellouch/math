import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section
noncomputable section

namespace SepticProfile.FamilyC1
open Set Metric
variable {A : Type*} [TopologicalSpace A]
abbrev V := ℂ × ℂ

/-- Continuous dependence of a polynomial family and its complex differential.
This is used only to obtain the uniform nonlinear bounds in the source sonic
contraction, not as a replacement for construction of the shooting family. -/
structure Data (h : A → V → ℂ) where
  D : A → V → V →L[ℂ] ℂ
  continuous_h : Continuous (fun p : A × V => h p.1 p.2)
  continuous_D : Continuous (fun p : A × V => D p.1 p.2)
  hasFD : ∀ a v, HasFDerivAt (h a) (D a v) v

namespace Data
variable {f g : A → V → ℂ}

def const (f : A → ℂ) (hf : Continuous f) : Data (fun a _ => f a) where
  D := fun _ _ => 0
  continuous_h := hf.comp continuous_fst
  continuous_D := continuous_const
  hasFD := fun _ _ => hasFDerivAt_const _ _

def fst : Data (fun _ : A => fun v : V => v.1) where
  D := fun _ _ => ContinuousLinearMap.fst ℂ ℂ ℂ
  continuous_h := continuous_fst.comp continuous_snd
  continuous_D := continuous_const
  hasFD := fun _ _ => hasFDerivAt_fst

def snd : Data (fun _ : A => fun v : V => v.2) where
  D := fun _ _ => ContinuousLinearMap.snd ℂ ℂ ℂ
  continuous_h := continuous_snd.comp continuous_snd
  continuous_D := continuous_const
  hasFD := fun _ _ => hasFDerivAt_snd

def add (F : Data f) (G : Data g) : Data (fun a v => f a v+g a v) where
  D := fun a v => F.D a v+G.D a v
  continuous_h := F.continuous_h.add G.continuous_h
  continuous_D := F.continuous_D.add G.continuous_D
  hasFD := fun a v => (F.hasFD a v).add (G.hasFD a v)

def neg (F : Data f) : Data (fun a v => -f a v) where
  D := fun a v => -F.D a v
  continuous_h := F.continuous_h.neg
  continuous_D := F.continuous_D.neg
  hasFD := fun a v => (F.hasFD a v).neg

def sub (F : Data f) (G : Data g) : Data (fun a v => f a v-g a v) where
  D := fun a v => F.D a v-G.D a v
  continuous_h := F.continuous_h.sub G.continuous_h
  continuous_D := F.continuous_D.sub G.continuous_D
  hasFD := fun a v => (F.hasFD a v).sub (G.hasFD a v)

def mul (F : Data f) (G : Data g) : Data (fun a v => f a v*g a v) where
  D := fun a v => f a v • G.D a v+g a v • F.D a v
  continuous_h := F.continuous_h.mul G.continuous_h
  continuous_D := (F.continuous_h.smul G.continuous_D).add (G.continuous_h.smul F.continuous_D)
  hasFD := fun a v => (F.hasFD a v).mul (G.hasFD a v)

def pow (F : Data f) (n : ℕ) : Data (fun a v => (f a v)^n) where
  D := fun a v => ((n:ℂ)*(f a v)^(n-1)) • F.D a v
  continuous_h := F.continuous_h.pow n
  continuous_D := (continuous_const.mul (F.continuous_h.pow (n-1))).smul F.continuous_D
  hasFD := fun a v => by simpa only [nsmul_eq_mul] using (F.hasFD a v).pow n

end Data

/-- The denominator cannot vanish in a uniform tube about the compact family
of origin points. No global zero-free condition is assumed. -/
lemma exists_uniform_den_radius [CompactSpace A] {d : A → V → ℂ}
    (hd : Continuous (fun p : A × V => d p.1 p.2)) (hn : ∀ a, d a 0 ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ a v, v ∈ closedBall 0 R → d a v ≠ 0 := by
  have hopen : IsOpen {p : A × V | d p.1 p.2 ≠ 0} := isOpen_ne_fun hd continuous_const
  have hsub : (univ : Set A) ×ˢ ({0} : Set V) ⊆ {p : A × V | d p.1 p.2 ≠ 0} := by
    rintro ⟨a,v⟩ ⟨_,hv⟩
    change d a v ≠ 0
    have hv' : v=0 := hv
    rw [hv']
    exact hn a
  obtain ⟨U,W,hU,hW,hAU,h0W,hUW⟩ := generalized_tube_lemma isCompact_univ isCompact_singleton hopen hsub
  obtain ⟨ε,hε,hεW⟩ := Metric.isOpen_iff.mp hW 0 (h0W (by simp))
  refine ⟨ε/2,by positivity,?_⟩
  intro a v hv
  exact hUW (show (a,v) ∈ U ×ˢ W from
    ⟨hAU (mem_univ a),hεW ((mem_closedBall.mp hv).trans_lt (by linarith))⟩)

end SepticProfile.FamilyC1

end
end

end OAI
