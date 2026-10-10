import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.HyperplaneHigh

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_high_peel_exceptions {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Range η σ D R →
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (g : ℝ) (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (H : Finset J) (hH : H.Nonempty) (Hyper : J→Submodule K (I→K))
      (X XH S : Finset (ℙ K (I→K))) (t : ℝ) (ht0 : 0<t)
      (O : ℙ K (I→K)→Finset (ℙ K (I→K)))
      (Lines Planes : Finset (Submodule K (I→K))) (Q : Finset (ℙ K (I→K))),
      2<q → Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      P η σ D R/10000<g → g≤σ →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀U : Submodule K (I→K),finrank K U=3 → ∃j∈F,Flat j=U) →
      (∀j∈H,finrank K (Hyper j)=4) →
      (∀U : Submodule K (I→K),finrank K U=4 → ∃j∈H,Hyper j=U) →
      (∀A∈Planes,finrank K A=3) →
      (X.card:ℝ)=Real.exp (2*σ+g) → (X.card:ℝ)≤10*Real.exp (5*σ/2) →
      XH=peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
        ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _) →
      t=(Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5) →
      S=peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht0) →
      Real.exp (2*σ+g)/4≤S.card →
      (∀x,ownCell F hF (fun j=>flatPoints (Flat j)) XH
        (peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht0)) x⊆O x) →
      (∀l∈Lines,finrank K l=2) →
      let O' := fun x=>S∩O x
      let rad := radialExceptions S O' (pointStrength S) Lines Q q X.card (P η σ D R/200)
      let pair := hyperplanePeelExceptions H hH Hyper X XH S Planes
        (peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
        (pointStrength S) (P η σ D R/200) Q
      ((rad∪pair).card:ℝ)≤(S.card:ℝ)*Real.exp (-L η σ D/1000)/2 := by
  have heR := eventually_exception_payment_wide hη hη' 0 2664192 16 (by norm_num) (by norm_num) (by norm_num)
  have heH := eventually_exception_payment_wide hη hη' 3145728 36872 16 (by norm_num) (by norm_num) (by norm_num)
  have ha := eventually_plane_ambient_margins hη hη'
  have hc := eventually_power_absorption hη hη' 33554432 0 (1/10000) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1000:ℝ),heR,heH,ha,hc] with σ hσ heR heH ha hc
  intro D R hr q K I J _ _ _ _ _ _ g F hF Flat H hH Hyper X XH S t ht0 O Lines Planes Q
    hq hcard hσq hI hg hg' hFlat hcover hHyper hHcover hPlanes hnX hori hXH ht hS hquarter hO hLines
  dsimp only
  have ha := ha D R hr
  let P := ParameterHierarchy.P η σ D R
  have hP : 0<P := by dsimp [P];linarith only [ha.1]
  have hg0 : 0≤g := by dsimp [P] at hP;linarith only [hg,hP]
  have hq0 : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hSn0 : (0:ℝ)<S.card := (by positivity : 0<Real.exp (2*σ+g)/4).trans_le hquarter
  have hHX : XH⊆X := hXH▸peel_subset (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X _ _
  have hSH : S⊆XH := hS▸peel_subset (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH _ _
  have hSX : (S.card:ℝ)≤X.card := Nat.cast_le.mpr (Finset.card_le_card (hSH.trans hHX))
  have hX : (XH.card:ℝ)≤Real.exp (2*σ+g) := by rw [←hnX];exact Nat.cast_le.mpr (Finset.card_le_card hHX)
  have hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3 := by
    have he : (10:ℝ)≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2),hσ]
    calc
      _≤10*Real.exp (5*σ/2) := hori
      _≤Real.exp (σ/2)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _=_ := by rw [hcard,←hσq,←Real.exp_nat_mul,←Real.exp_add];congr 1;norm_num;ring
  have hcardS : (S.card:ℝ)≤Real.exp (3*σ) := by
    apply hSX.trans
    rw [←show (Nat.card K:ℝ)^3=Real.exp (3*σ) by rw [hcard,←hσq,←Real.exp_nat_mul];norm_num]
    exact hcap
  have hδ : (pointStrength (K:=K) S:ℝ)=(q:ℝ)/S.card := by simp only [pointStrength,NNReal.coe_div,NNReal.coe_natCast,hcard]
  have hδ0 : 0<pointStrength (K:=K) S := by rw [←NNReal.coe_pos,hδ];positivity
  have heq : 3*σ/2+(g+σ/2)=2*σ+g := by ring
  have hrad := literal_plane_radial_exceptions hq hcard (Or.inr hI) σ (g+σ/2) (P/10000) (P/200) hσq hσ
    ha.1 (by linarith only [hP]) (by linarith only [hg',hσ]) F hF Flat hFlat hcover XH (by rwa [heq])
    t (by rwa [heq]) ht0 S hS (by rwa [heq]) O hO (pointStrength S) hδ Lines hLines Q
  rw [heq,←hnX] at hrad
  have hpayR := heR D R g (P/200) S.card hr hg.le (le_refl _) hcardS
  simp only [zero_mul,zero_add] at hpayR
  have hrad' : ((radialExceptions S (fun x=>S∩O x) (pointStrength S) Lines Q q X.card (P/200)).card:ℝ)≤
      (S.card:ℝ)*Real.exp (-L η σ D/1000)/4 := by
    calc
      _≤(X.card:ℝ)*(2664192*((Nat.clog 2 S.card:ℝ)+1)*Real.exp (-P/200)) := by simpa only [neg_div] using hrad
      _=(X.card:ℝ)*(((Nat.clog 2 S.card:ℝ)+1)*(2664192*Real.exp (-P/200))) := by ring
      _≤(X.card:ℝ)*(Real.exp (-L η σ D/1000)/16) := mul_le_mul_of_nonneg_left (by simpa only [neg_div] using hpayR) (Nat.cast_nonneg _)
      _≤_ := by rw [hnX];nlinarith only [mul_le_mul_of_nonneg_right hquarter (Real.exp_nonneg (-L η σ D/1000))]
  have hhigh' : 8388608*(Nat.card K:ℝ)^2≤S.card := by
    have hc : (33554432:ℝ)≤Real.exp (P/10000) := by
      simpa only [P,Real.rpow_zero,mul_one,one_div,one_mul,mul_comm (10000⁻¹:ℝ),div_eq_mul_inv] using hc D R hr
    have hc := hc.trans (Real.exp_le_exp.mpr hg.le)
    have hnq : Real.exp (2*σ+g)=(Nat.card K:ℝ)^2*Real.exp g := by
      rw [hcard,←hσq,←Real.exp_nat_mul,←Real.exp_add];norm_num
    rw [hnq] at hquarter
    nlinarith only [mul_le_mul_of_nonneg_right hc (sq_nonneg (Nat.card K:ℝ)),hquarter]
  have hori' : (X.card:ℝ)^2≤100*(Nat.card K:ℝ)^5 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) hori 2
    apply hh.trans_eq
    rw [mul_pow,←Real.exp_nat_mul,hcard,←hσq,←Real.exp_nat_mul]
    congr 1
    norm_num
    ring_nf
  have hnq : (X.card:ℝ)=(Nat.card K:ℝ)^2*Real.exp g := by
    rw [hnX,hcard,←hσq,←Real.exp_nat_mul,←Real.exp_add];norm_num
  have hpair := hyperplanePeelExceptions_card H hH Hyper X XH S Planes hHyper hHcover hPlanes
    (P/10000<g) hg hXH hSH (pointStrength S) hδ0 (P/200) g hg0 (by positivity)
    hnq hcap hori' hhigh' Q
  have hpayH := heH D R g (P/200) S.card hr hg.le (le_refl _) hcardS
  have hpair' : ((hyperplanePeelExceptions H hH Hyper X XH S Planes
      (peelLength (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
      (pointStrength S) (P/200) Q).card:ℝ)≤(S.card:ℝ)*Real.exp (-L η σ D/1000)/4 := by
    calc
      _≤(X.card:ℝ)*(((Nat.clog 2 S.card:ℝ)+1)*(3145728*Real.exp (-(4/5:ℝ)*g)+36872*Real.exp (-(P/200)))) := by simpa only [mul_assoc] using hpair
      _≤(X.card:ℝ)*(Real.exp (-L η σ D/1000)/16) := mul_le_mul_of_nonneg_left hpayH (Nat.cast_nonneg _)
      _≤_ := by rw [hnX];nlinarith only [mul_le_mul_of_nonneg_right hquarter (Real.exp_nonneg (-L η σ D/1000))]
  have hh := Nat.cast_le (α:=ℝ).mpr (Finset.card_union_le
    (radialExceptions S (fun x=>S∩O x) (pointStrength S) Lines Q q X.card (P/200))
    (hyperplanePeelExceptions H hH Hyper X XH S Planes
      (peelLength (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
      (pointStrength S) (P/200) Q))
  push_cast at hh
  linarith only [hh,hrad',hpair']
end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma radialExceptions_chi_mono (S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (δ : ℝ≥0) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V))
    (q n χ ψ : ℝ) (h : χ≤ψ) :
    radialExceptions S O δ Lines Q q n ψ⊆radialExceptions S O δ Lines Q q n χ := by
  intro x hx
  obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
  apply Finset.mem_biUnion.mpr
  refine ⟨i,hi,badCenters_threshold_mono S O δ _ Lines Q ?_ hx⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) (by positivity)

lemma mem_badCenters_own_congr (S : Finset (ℙ K V)) (O O' : ℙ K V→Finset (ℙ K V))
    (δ a : ℝ) (Lines : Finset (Submodule K V)) (Q : Finset (ℙ K V)) (B : ℝ)
    (x : ℙ K V) (h : O x=O' x) :
    x∈badCenters S O δ a Lines Q B ↔ x∈badCenters S O' δ a Lines Q B := by
  simp only [badCenters,Finset.mem_filter,localLines,richCenters]
  rw [h]
end SharpRamseyFive.ScoreGeometry

end OAI
