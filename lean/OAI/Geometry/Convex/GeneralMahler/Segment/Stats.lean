import OAI.Geometry.Convex.GeneralMahler.Scalar.LayerProof
import OAI.Geometry.Convex.GeneralMahler.Scalar.Integr

namespace OAI
noncomputable section
open Set Filter MeasureTheory Real
namespace GeneralMahler.SCal.SE
open Grid Tag Profile Cert Cert.IV
lemma hK (h:NG) (x:ℝ):
    -70/10000 ≤ Kp (xs x) ∧ Kp (xs x) ≤ 275/10000 := by
  have hh := mRange h x K
  rw [rng,mem_band] at hh
  change _≤ Kp (xs x) ∧ Kp (xs x) ≤_ at hh
  norm_num at *; exact hh
lemma hKe (h:NG) (x:ℝ) (hi:14/10≤|x|):
    -1/10000 ≤ Kp (xs x) ∧ Kp (xs x) ≤ 191/10000 := by
  have hh := mOff h x (by norm_num [nd] at *; linarith) K
  rw [roff,mem_band] at hh
  change _≤ Kp (xs x) ∧ Kp (xs x) ≤_ at hh
  norm_num at *; exact hh
lemma hC (h:NG) (x:ℝ):
    -5010/10000 ≤ Cp (xs x) ∧ Cp (xs x) ≤ -3410/10000 := by
  have hh := mRange h x C
  rw [rng,mem_band] at hh
  change _≤ Cp (xs x) ∧ Cp (xs x) ≤_ at hh
  norm_num at *; exact hh
lemma hCe (h:NG) (x:ℝ) (hi:14/10≤|x|):
    -5010/10000 ≤ Cp (xs x) ∧ Cp (xs x) ≤ -4950/10000 := by
  have hh := mOff h x (by norm_num [nd] at *; linarith) C
  rw [roff,mem_band] at hh
  change _≤ Cp (xs x) ∧ Cp (xs x) ≤_ at hh
  norm_num at *; exact hh
lemma hQ (h:NG) (x:ℝ):
    775/10000 ≤ qu (xs x) ∧ qu (xs x) ≤ 2559/10000 := by
  have hh := mRange h x Q
  rw [rng,mem_band] at hh
  change _≤ qu (xs x) ∧ qu (xs x) ≤_ at hh
  norm_num at *; exact hh
lemma hQe (h:NG) (x:ℝ) (hi:14/10≤|x|):
    2350/10000 ≤ qu (xs x) ∧ qu (xs x) ≤ 2559/10000 := by
  have hh := mOff h x (by norm_num [nd] at *; linarith) Q
  rw [roff,mem_band] at hh
  change _≤ qu (xs x) ∧ qu (xs x) ≤_ at hh
  norm_num at *; exact hh
lemma hdK (h:NG) (x:ℝ):
    -660/10000 ≤ DotF Kp x ∧ DotF Kp x ≤ 660/10000 := by
  have hh := mRange h x dK
  rw [rng,mem_band] at hh
  change _≤ DotF Kp x ∧ DotF Kp x ≤_ at hh
  norm_num at *; exact hh
lemma hdKe (h:NG) (x:ℝ) (hi:14/10≤|x|):
    -211/10000 ≤ DotF Kp x ∧ DotF Kp x ≤ 211/10000 := by
  have hh := mOff h x (by norm_num [nd] at *; linarith) dK
  rw [roff,mem_band] at hh
  change _≤ DotF Kp x ∧ DotF Kp x ≤_ at hh
  norm_num at *; exact hh
lemma hdC (h:NG) (x:ℝ):
    -2470/10000 ≤ DotF Cp x ∧ DotF Cp x ≤ 2470/10000 := by
  have hh := mRange h x dC
  rw [rng,mem_band] at hh
  change _≤ DotF Cp x ∧ DotF Cp x ≤_ at hh
  norm_num at *; exact hh
lemma hdCe (h:NG) (x:ℝ) (hi:14/10≤|x|):
    -84/10000 ≤ DotF Cp x ∧ DotF Cp x ≤ 84/10000 := by
  have hh := mOff h x (by norm_num [nd] at *; linarith) dC
  rw [roff,mem_band] at hh
  change _≤ DotF Cp x ∧ DotF Cp x ≤_ at hh
  norm_num at *; exact hh
lemma hdQ (h:NG) (x:ℝ):
    -1930/10000 ≤ DotF qu x ∧ DotF qu x ≤ 1930/10000 := by
  have hh := mRange h x dQ
  rw [rng,mem_band] at hh
  change _≤ DotF qu x ∧ DotF qu x ≤_ at hh
  norm_num at *; exact hh
lemma hddK (h:NG) (x:ℝ):
    -2600/10000 ≤ DDot Kp x ∧ DDot Kp x ≤ 2600/10000 := by
  have hh := mRange h x ddK
  rw [rng,mem_band] at hh
  change _≤ DDot Kp x ∧ DDot Kp x ≤_ at hh
  norm_num at *; exact hh
lemma hddC (h:NG) (x:ℝ):
    -9500/10000 ≤ DDot Cp x ∧ DDot Cp x ≤ 9500/10000 := by
  have hh := mRange h x ddC
  rw [rng,mem_band] at hh
  change _≤ DDot Cp x ∧ DDot Cp x ≤_ at hh
  norm_num at *; exact hh
lemma hddQ (h:NG) (x:ℝ):
    -5600/10000 ≤ DDot qu x ∧ DDot qu x ≤ 5600/10000 := by
  have hh := mRange h x ddQ
  rw [rng,mem_band] at hh
  change _≤ DDot qu x ∧ DDot qu x ≤_ at hh
  norm_num at *; exact hh
lemma hNK (h:NG) (x:ℝ):
    -3000/10000 ≤ NNf Kp x ∧ NNf Kp x ≤ 3000/10000 := by
  have hh := mRange h x NK
  rw [rng,mem_band] at hh
  change _≤ NNf Kp x ∧ NNf Kp x ≤_ at hh
  norm_num at *; exact hh
lemma hNKe (h:NG) (x:ℝ) (hi:14/10≤|x|):
    0/10000 ≤ NNf Kp x ∧ NNf Kp x ≤ 3000/10000 := by
  have hh := mOff h x (by norm_num [nd] at *; linarith) NK
  rw [roff,mem_band] at hh
  change _≤ NNf Kp x ∧ NNf Kp x ≤_ at hh
  norm_num at *; exact hh
lemma hNC (h:NG) (x:ℝ):
    -9500/10000 ≤ NNf Cp x ∧ NNf Cp x ≤ 9500/10000 := by
  have hh := mRange h x NC
  rw [rng,mem_band] at hh
  change _≤ NNf Cp x ∧ NNf Cp x ≤_ at hh
  norm_num at *; exact hh
lemma hNQ (h:NG) (x:ℝ):
    -5600/10000 ≤ NNf qu x ∧ NNf qu x ≤ 5600/10000 := by
  have hh := mRange h x NQ
  rw [rng,mem_band] at hh
  change _≤ NNf qu x ∧ NNf qu x ≤_ at hh
  norm_num at *; exact hh
lemma ValY (h:NG) (x:ℝ)(hi:36/10 ≤ x):
    0 ≤ Kp (xs x) ∧ Kp (xs x) ≤ 8/10000 ∧
      -5002/10000 ≤ Cp (xs x) ∧ Cp (xs x) ≤ -4998/10000 ∧
      255/1000 ≤ qu (xs x) ∧ qu (xs x) ≤ 2556/10000 := by
  have he : nd 720≤x:= by norm_num [nd] at *; exact hi
  obtain ⟨y,hx,hj⟩:= find_tail he
  have hp(i):=Tail.tag_tail hx hj (hrq h) (hqt h) i
  have h0 : Kp (xs x)∈band 0 8:=hp K
  have hb:=Tail.tailXCheck
  simp only [Bool.and_eq_true] at hb
  have narrow (i : Tag) {B : IV} (hB : SubB (Tail.tabT i) B = true) :
      i.act x ∈ B := subB (hp i) hB
  have h1 : Cp (xs x)∈band (-5002) (-4998):= narrow C hb.1
  have h2 : qu (xs x)∈band 2550 2556:=narrow Q hb.2
  rw [mem_band] at h0 h1 h2
  norm_num at *
  exact ⟨h0.1,h0.2,h1.1,h1.2,h2⟩

variable {f:ℝ→ℝ}
lemma liftD (hf:TestF f)(x:ℝ): HasDerivAt (liftF f) (DotF f x) x := (d_lift hf _).differentiableAt.hasDerivAt
lemma Dt_cont (hf:TestF f): Continuous (DotF f) :=
  continuous_iff_continuousAt.mpr fun x=> (dd_lift hf x).continuousAt
lemma nn_cont (hf:TestF f): Continuous (NNf f):= by
  have hh : NNf f=fun x=>ast x^2*deriv (deriv f) (xs x):=funext fun x=>(SCov f hf x).1
  rw [hh]
  have ha : Continuous ast:=by unfold ast; fun_prop
  have hb : Continuous xs:=by unfold xs; fun_prop
  exact (ha.pow _).mul (hf.der.der.cont.comp hb)
lemma dist_bdd {x y:ℝ} (hf:TestF f)(L:ℝ) (he:x≤y) (hb:∀ t∈Icc x y,|DotF f t| ≤ L):
    |f (xs y)-f (xs x)|≤ L*(y-x):= by
  rcases he.eq_or_lt with h|h
  · subst y; simp
  obtain ⟨t,ht,hz⟩:= exists_deriv_eq_slope (liftF f) h
    ((show Continuous _ from continuous_iff_continuousAt.mpr fun x=>(d_lift hf x).continuousAt).continuousOn)
    (fun x _=>(d_lift hf x).differentiableAt.differentiableWithinAt)
  rw [eq_div_iff (sub_pos.mpr h).ne'] at hz
  change |liftF f y-liftF f x|≤ _
  rw [← hz,abs_mul,abs_of_pos (sub_pos.mpr h)]
  exact mul_le_mul_of_nonneg_right (hb t ⟨ht.1.le,ht.2.le⟩) (sub_pos.mpr h).le
end GeneralMahler.SCal.SE

end

end OAI
