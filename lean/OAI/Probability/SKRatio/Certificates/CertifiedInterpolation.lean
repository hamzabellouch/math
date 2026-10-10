import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedInterval
import OAI.Probability.SKRatio.Variational.ScalarInterpolation

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

namespace Box

def posInv (A : Box) : Box := round (1/A.hi) (1/A.lo)
def divPos (A B : Box) : Box := mul A (posInv B)
lemma mem_divPos {A B : Box} {x y : ℝ} (hx : x ∈ A) (hy : y ∈ B)
    (hB : 0 < B.lo) : x/y ∈ divPos A B := by
  have hi : inv B=some (posInv B) := by simp only [inv,posInv,ite_eq_left hB]
  exact mem_mul hx (mem_inv hy hi).1

lemma lower {A : Box} {q : ℚ} {x : ℝ} (h : q ≤ A.lo) (hx : x ∈ A) : (q:ℝ) ≤ x :=
  (by exact_mod_cast h : (q:ℝ) ≤ A.lo).trans hx.1
lemma upper {A : Box} {q : ℚ} {x : ℝ} (h : A.hi ≤ q) (hx : x ∈ A) : x ≤ (q:ℝ) :=
  hx.2.trans (by exact_mod_cast h)
end Box

structure Enclosures where
  av : Box
  gv : Box
  mv : Box
  rv : Box
  vs : Box
  gs : Box
  ms : Box
  fs : Box

structure Valid (β : ℝ) (X : Enclosures) : Prop where
  mem_a : a β ∈ X.av
  mem_G : G β ∈ X.gv
  mem_M : (∫ h, m h*v h ∂fieldLaw β) ∈ X.mv
  mem_R : R β ∈ X.rv
  mem_v : sd (fieldLaw β) v ∈ X.vs
  mem_g : sd (fieldLaw β) g ∈ X.gs
  mem_mv : sd (fieldLaw β) (fun h => m h*v h) ∈ X.ms
  mem_F : sd (fieldLaw β) (F β) ∈ X.fs

def lBox (A : Box) : Box := Box.sub (Box.rat (64/100)) (Box.mul (Box.rat (19/100)) A)
lemma mem_lBox {β : ℝ} {A : Box} (ha : a β ∈ A) : l β ∈ lBox A := by
  rw [l_eq]
  simpa only [lBox,Rat.cast_div,Rat.cast_ofNat] using
    Box.mem_sub (Box.mem_rat (64/100)) (Box.mem_mul (Box.mem_rat (19/100)) ha)

def coefficientBox (X Y : Enclosures) : Box :=
  Box.sub (Box.sub (Box.divPos (Box.sq Y.av) (lBox Y.av)) Y.av)
    (Box.mul (Box.rat (3/2)) (Box.sq X.gv))

def slackBox₀ (j z : ℚ) (X Y : Enclosures) : Box :=
  Box.sub (Box.add (Box.add (lBox X.av) (Box.rat (18/1000)))
    (Box.mul (Box.rat (j^2)) (coefficientBox X Y))) (Box.mul (Box.rat (z^2)) Y.rv)

def slackBox₁ (j z : ℚ) (X Y : Enclosures) : Box :=
  Box.sub (Box.add (Box.sub (Box.rat (4644/10000)) (Box.mul (Box.rat (z/2)) Y.vs))
    (Box.mul (Box.rat (j^2)) X.mv))
    (Box.mul (Box.rat (z^2)) (Box.add (Box.mul (Box.rat (3/2)) (Box.sq Y.gs)) Y.rv))

def crossBox (j z t : ℚ) (X Y : Enclosures) : Box :=
  let aTerm := Box.mul (Box.sub X.av Y.av) (Box.rat z)
  let mTerm := Box.mul (Box.rat (2*(z^2-j^2))) Y.ms
  let vTerm := Box.mul (Box.sub (Box.divPos (Box.mul (Box.rat (z^2)) X.av) (lBox X.av))
    (Box.divPos (Box.mul (Box.rat (j^2)) Y.av) (lBox Y.av))) Y.vs
  let gTerm := Box.mul (Box.mul (Box.rat 3)
    (Box.sub (Box.mul (Box.rat (z^2)) X.gv) (Box.mul (Box.rat (j^2)) Y.gv))) Y.gs
  Box.mul ⟨0,t⟩ (Box.add (Box.add (Box.add (Box.add Y.fs aTerm) mTerm) vTerm) gTerm)

lemma coefficient_mem {j z : ℝ} {X Y : Enclosures} (hx : Valid j X) (hy : Valid z Y)
    (hY : 0 < (lBox Y.av).lo) : a z^2/l z-a z-(3/2)*G j^2 ∈ coefficientBox X Y := by
  simpa only [coefficientBox,Rat.cast_div,Rat.cast_ofNat] using Box.mem_sub
    (Box.mem_sub (Box.mem_divPos (Box.mem_sq hy.mem_a) (mem_lBox hy.mem_a) hY) hy.mem_a)
    (Box.mem_mul (Box.mem_rat (3/2)) (Box.mem_sq hx.mem_G))

lemma slack₀_mem {j z : ℚ} {X Y : Enclosures} (hx : Valid j X) (hy : Valid z Y)
    (hY : 0 < (lBox Y.av).lo) : slackBound₀ j z ∈ slackBox₀ j z X Y := by
  have hh := Box.mem_sub
    (Box.mem_add (Box.mem_add (mem_lBox hx.mem_a) (Box.mem_rat (18/1000)))
      (Box.mem_mul (Box.mem_rat (j^2)) (coefficient_mem hx hy hY)))
    (Box.mem_mul (Box.mem_rat (z^2)) hy.mem_R)
  rw [Rat.cast_pow,Rat.cast_pow] at hh
  simpa only [slackBound₀,slackBox₀,Rat.cast_div,Rat.cast_ofNat] using hh

lemma slack₁_mem {j z : ℚ} {X Y : Enclosures} (hx : Valid j X) (hy : Valid z Y) :
    slackBound₁ j z ∈ slackBox₁ j z X Y := by
  have hh := Box.mem_sub
    (Box.mem_add (Box.mem_sub (Box.mem_rat (4644/10000))
      (Box.mem_mul (Box.mem_rat (z/2)) hy.mem_v))
      (Box.mem_mul (Box.mem_rat (j^2)) hx.mem_M))
    (Box.mem_mul (Box.mem_rat (z^2))
      (Box.mem_add (Box.mem_mul (Box.mem_rat (3/2)) (Box.mem_sq hy.mem_g)) hy.mem_R))
  simp only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] at hh
  convert! hh using 1
  unfold slackBound₁
  ring

lemma cross_mem {j z t : ℚ} {X Y : Enclosures} (hx : Valid j X) (hy : Valid z Y)
    (hX : 0 < (lBox X.av).lo) (hY : 0 < (lBox Y.av).lo)
    (ht : sqrt (densityFactor j z) ≤ (t:ℝ)) : crossBound j z ∈ crossBox j z t X Y := by
  have ht' : sqrt (densityFactor j z) ∈ (⟨0,t⟩ : Box) := by
    exact ⟨by simpa only [Rat.cast_zero] using sqrt_nonneg _,ht⟩
  have hh := Box.mem_mul ht' (Box.mem_add (Box.mem_add (Box.mem_add
      (Box.mem_add hy.mem_F (Box.mem_mul (Box.mem_sub hx.mem_a hy.mem_a) (Box.mem_rat z)))
        (Box.mem_mul (Box.mem_rat (2*(z^2-j^2))) hy.mem_mv))
        (Box.mem_mul (Box.mem_sub
          (Box.mem_divPos (Box.mem_mul (Box.mem_rat (z^2)) hx.mem_a) (mem_lBox hx.mem_a) hX)
          (Box.mem_divPos (Box.mem_mul (Box.mem_rat (j^2)) hy.mem_a) (mem_lBox hy.mem_a) hY)) hy.mem_v))
        (Box.mem_mul (Box.mem_mul (Box.mem_rat 3)
          (Box.mem_sub (Box.mem_mul (Box.mem_rat (z^2)) hx.mem_G)
            (Box.mem_mul (Box.mem_rat (j^2)) hy.mem_G))) hy.mem_g))
  repeat rw [Rat.cast_mul] at hh
  repeat rw [Rat.cast_sub] at hh
  repeat rw [Rat.cast_pow] at hh
  simpa only [crossBound,crossBox,Rat.cast_div,Rat.cast_ofNat] using hh

def interpolationCheck (j z t : ℚ) (X Y : Enclosures) : Bool := decide (
  0 < (lBox X.av).lo ∧ 0 < (lBox Y.av).lo ∧
  (lBox Y.av).hi ≤ 2*Y.av.lo ∧ 0 ≤ (coefficientBox X Y).lo ∧
  511/1000 ≤ (slackBox₀ j z X Y).lo ∧ 425/1000 ≤ (slackBox₁ j z X Y).lo ∧
  (crossBox j z t X Y).hi ≤ 925/1000)

lemma interpolation_check_sound {j z t : ℚ} {X Y : Enclosures}
    (hx : Valid j X) (hy : Valid z Y)
    (ht : sqrt (densityFactor j z) ≤ (t:ℝ))
    (hc : interpolationCheck j z t X Y = true) :
    l z ≤ 2*a z ∧ 0 ≤ a z^2/l z-a z-(3/2)*G j^2 ∧
    511/1000 ≤ slackBound₀ j z ∧ 425/1000 ≤ slackBound₁ j z ∧ crossBound j z ≤ 925/1000 := by
  rcases of_decide_eq_true hc with ⟨hX,hY,hreg,hcoeff,hS₀,hS₁,hC⟩
  have hreg' : ((lBox Y.av).hi:ℝ) ≤ 2*(Y.av.lo:ℝ) := by exact_mod_cast hreg
  have hreg'' : l (z:ℝ) ≤ 2*a z := by
    linarith only [(mem_lBox hy.mem_a).2,hy.mem_a.1,hreg']
  refine ⟨hreg'',?_,?_,?_,?_⟩
  · simpa only [Rat.cast_zero] using Box.lower hcoeff (coefficient_mem hx hy hY)
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using Box.lower hS₀ (slack₀_mem hx hy hY)
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using Box.lower hS₁ (slack₁_mem hx hy)
  · simpa only [Rat.cast_div,Rat.cast_ofNat] using Box.upper hC (cross_mem hx hy hX hY ht)

lemma certified_slacks {j z t : ℚ} {X Y : Enclosures} {β : ℝ}
    (hj : 0 < (j:ℝ)) (hjβ : (j:ℝ) ≤ β) (hβz : β ≤ (z:ℝ)) (hz : (z:ℝ) ≤ 1)
    (hx : Valid j X) (hy : Valid z Y) (ht : sqrt (densityFactor j z) ≤ (t:ℝ))
    (hc : interpolationCheck j z t X Y = true) :
    511/1000 ≤ U₀ β ∧ 425/1000 ≤ U₁ β ∧ sd (fieldLaw β) (F β) ≤ 925/1000 := by
  obtain ⟨hreg,hcoeff,hS₀,hS₁,hC⟩ := interpolation_check_sound hx hy ht hc
  exact ⟨hS₀.trans (U₀_interval hj hjβ hβz hz hreg hcoeff),
    hS₁.trans (U₁_interval hj hjβ hβz hz),(sd_F_interval hj hjβ hβz).trans hC⟩

lemma discriminant_of_slacks {β : ℝ} (h0 : 511/1000 ≤ U₀ β)
    (h1 : 425/1000 ≤ U₁ β) (hs : sd (fieldLaw β) (F β) ≤ 925/1000) :
    0 < U₀ β ∧ sd (fieldLaw β) (F β)^2 ≤ 4*U₀ β*U₁ β := by
  have h0p : 0 < U₀ β := by linarith
  have hp := mul_le_mul h0 h1 (by norm_num : (0:ℝ) ≤ 425/1000) h0p.le
  have hsq := (sq_le_sq₀ (sd_nonneg (μ := fieldLaw β) (F β))
    (by norm_num : (0:ℝ) ≤ 925/1000)).mpr hs
  exact ⟨h0p,by nlinarith only [hp,hsq]⟩

end SKRatio.Certificate

end

end OAI
