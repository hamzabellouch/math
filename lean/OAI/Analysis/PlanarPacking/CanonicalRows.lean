import OAI.Analysis.PlanarPacking.BasisIntervals
import OAI.Analysis.PlanarPacking.Nodes

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerIntervals

def CBox.SqNormCheck (a : CBox) (m n : ℤ) : Prop :=
  0 < n ∧ 0 ≤ m ∧ (a.re.bound^2+a.im.bound^2)*n^2 ≤ (precision*m)^2
instance (a : CBox) (m n : ℤ) : Decidable (a.SqNormCheck m n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

lemma CBox.norm_le_rat {a : CBox} {z : ℂ} {m n : ℤ} (hz : a.Contains z)
    (hc : a.SqNormCheck m n) : ‖z‖ ≤ (m:ℝ)/n := by
  have hn : (0:ℝ) < n := by exact_mod_cast hc.1
  have hm : (0:ℝ) ≤ m := by exact_mod_cast hc.2.1
  have hr := RBox.abs_bound hz.1
  have hi := RBox.abs_bound hz.2
  have hb1 : (0:ℝ) ≤ a.re.bound := (mul_nonneg precision_pos.le (abs_nonneg _)).trans hr
  have hb2 : (0:ℝ) ≤ a.im.bound := (mul_nonneg precision_pos.le (abs_nonneg _)).trans hi
  have hs1 : (precision:ℝ)^2*z.re^2 ≤ (a.re.bound:ℝ)^2 := by
    simpa only [mul_pow, sq_abs] using
      (sq_le_sq₀ (mul_nonneg precision_pos.le (abs_nonneg _)) hb1).mpr hr
  have hs2 : (precision:ℝ)^2*z.im^2 ≤ (a.im.bound:ℝ)^2 := by
    simpa only [mul_pow, sq_abs] using
      (sq_le_sq₀ (mul_nonneg precision_pos.le (abs_nonneg _)) hb2).mpr hi
  have hh : (((a.re.bound:ℝ)^2+(a.im.bound:ℝ)^2)*(n:ℝ)^2) ≤ ((precision:ℝ)*m)^2 := by
    exact_mod_cast hc.2.2
  have he : ‖z‖^2 = z.re^2+z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  have hk : ((precision:ℝ)*‖z‖)^2 ≤ (a.re.bound:ℝ)^2+(a.im.bound:ℝ)^2 := by
    rw [mul_pow,he]; nlinarith only [hs1,hs2]
  have hkn := mul_le_mul_of_nonneg_right hk (sq_nonneg (n:ℝ))
  have hbound : (‖z‖*(n:ℝ))^2 ≤ (m:ℝ)^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos precision_pos)).mp
    nlinarith only [hkn,hh]
  apply (le_div_iff₀ hn).mpr
  nlinarith only [hbound,mul_nonneg (norm_nonneg z) hn.le,hm]

end SharpPlanar.IntegerIntervals

namespace SharpPlanar


noncomputable def lambdaCap : Fin 7 → ℝ := ![2887/1000,2665/1000,2218/1000,1804/1000,1486/1000,1250/1000,1073/1000]
noncomputable def zCap : Fin 7 → ℝ := ![2934/1000,2713/1000,2269/1000,1859/1000,1548/1000,1320/1000,1151/1000]
noncomputable def dampingCap : Fin 7 → ℝ := ![2933/1000,2440/1000,1567/1000,900/1000,482/1000,224/1000,597/10000]
noncomputable def slopeCap : Fin 6 → ℝ := ![0,48/10,317/100,1946/1000,1217/1000,792/1000]

lemma kernel_den_sq (t : ℝ) : ‖(t:ℂ)+Complex.I*h‖^2 = t^2+h^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,pow_two]
lemma z_re (t : ℝ) : (z t).re = -B*t/(t^2+h^2) := by
  simp [z,Complex.div_re,Complex.normSq_apply,pow_two]
lemma lambda_sq (t : ℝ) : ‖lambda t‖^2 = (4/3:ℝ)/(t^2+h^2) := by
  rw [lambda,norm_div,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos b_pos,div_pow,mul_pow,kernel_den_sq,b_sq]
  field_simp
lemma z_sq (t : ℝ) : ‖z t‖^2 = (4/25:ℝ)+(304/225:ℝ)/(t^2+h^2) := by
  have hd : t^2+h^2 ≠ 0 := ne_of_gt (by unfold h; positivity : 0 < t^2+h^2)
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,z_re,z_im]
  dsimp [B,h] at hd ⊢
  field_simp
  ring

lemma lambda_sq_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖lambda t‖^2 ≤ ‖lambda s‖^2 := by
  rw [lambda_sq,lambda_sq]
  apply div_le_div_of_nonneg_left (by norm_num) (by unfold h; positivity)
  nlinarith
lemma z_sq_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖z t‖^2 ≤ ‖z s‖^2 := by
  rw [z_sq,z_sq]
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_left (by norm_num) (by unfold h; positivity)
  nlinarith

lemma endpoint_kernel_bounds (j : Fin 7) :
    ‖lambda ((j.val:ℝ)/6)‖ ≤ lambdaCap j ∧
    ‖z ((j.val:ℝ)/6)‖ ≤ zCap j ∧
    dampingCap j ≤ (z ((j.val:ℝ)/6)).im := by
  have hb : 0 ≤ lambdaCap j := by fin_cases j <;> norm_num [lambdaCap]
  have ha : 0 ≤ zCap j := by fin_cases j <;> norm_num [zCap]
  refine ⟨(sq_le_sq₀ (norm_nonneg _) hb).mp ?_,(sq_le_sq₀ (norm_nonneg _) ha).mp ?_,?_⟩
  · rw [lambda_sq]; fin_cases j <;> norm_num [lambdaCap,h]
  · rw [z_sq]; fin_cases j <;> norm_num [zCap,h]
  · rw [z_im]; fin_cases j <;> norm_num [dampingCap,h,B]

lemma piece_secant_bound (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    slopeCap j*(t^2+h^2)*((((j.val:ℝ)+1)/6)^2+h^2) ≤
      h*B*(t+((j.val:ℝ)+1)/6) := by
  have hp := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)
  fin_cases j <;> norm_num [slopeCap,h,B] at * <;> nlinarith

lemma piece_damping_bound (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    dampingCap ⟨j.val+1,by omega⟩+slopeCap j*(((j.val:ℝ)+1)/6-t) ≤ (z t).im := by
  let u : ℝ := ((j.val:ℝ)+1)/6
  have hd : 0 < t^2+h^2 := by unfold h; positivity
  have hu : 0 < u^2+h^2 := by unfold h; positivity
  have hid : ((z t).im-(z u).im)*(t^2+h^2)*(u^2+h^2) = h*B*(u-t)*(u+t) := by
    rw [z_im,z_im]
    field_simp
    ring
  have hs := mul_le_mul_of_nonneg_right (piece_secant_bound j ht) (sub_nonneg.mpr ht.2)
  have hm : slopeCap j*(u-t) ≤ (z t).im-(z u).im := by
    apply (mul_le_mul_iff_right₀ (mul_pos hd hu)).mp
    dsimp [u] at hid ⊢
    nlinarith only [hs,hid]
  have he := (endpoint_kernel_bounds ⟨j.val+1,by omega⟩).2.2
  simp only [Nat.cast_add,Nat.cast_one] at he
  change dampingCap ⟨j.val+1,by omega⟩ ≤ (z u).im at he
  dsimp [u] at hm he
  linarith only [hm,he]


lemma piece_kernel_bounds (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖lambda t‖ ≤ lambdaCap ⟨j.val,by omega⟩ ∧
    ‖z t‖ ≤ zCap ⟨j.val,by omega⟩ ∧
    dampingCap ⟨j.val+1,by omega⟩+slopeCap j*(((j.val:ℝ)+1)/6-t) ≤ (z t).im := by
  have hs : 0 ≤ (j.val:ℝ)/6 := by positivity
  have hb := (endpoint_kernel_bounds ⟨j.val,by omega⟩).1
  have ha := (endpoint_kernel_bounds ⟨j.val,by omega⟩).2.1
  refine ⟨?_,?_,piece_damping_bound j ht⟩
  · exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (lambda_sq_antitone hs ht.1)).trans hb
  · exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (z_sq_antitone hs ht.1)).trans ha

end SharpPlanar

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

noncomputable def uAmplitude (n j : ℕ) (t : ℝ) : ℂ :=
  -2*(Real.pi:ℂ)^2*(basisBeta n j-(t:ℂ)*basisAlpha n j)
noncomputable def vAmplitude (n j : ℕ) : ℂ :=
  2*Complex.I*Real.pi*basisAlpha n j

def uAmplitudeBox (t : RBox) (a b : CBox) : CBox :=
  ((rcast (piBounds.mul piBounds)).scale (-2) 1).mul
    (b.add (((rcast t).mul a).neg))
def vAmplitudeBox (a : CBox) : CBox := (piI.scale 2 1).mul a

lemma uAmplitudeBox_contains {t : RBox} {a b : CBox} {s : ℝ} {n j : ℕ}
    (ht : t.Contains s) (ha : a.Contains (basisAlpha n j)) (hb : b.Contains (basisBeta n j)) :
    (uAmplitudeBox t a b).Contains (uAmplitude n j s) := by
  have hp := CBox.contains_scale (rcast_contains
    (RBox.contains_mul piBounds_contains piBounds_contains)) (-2) 1 (by norm_num)
  have he := CBox.contains_mul hp
    (CBox.contains_add hb (CBox.neg_contains (CBox.contains_mul (rcast_contains ht) ha)))
  unfold uAmplitudeBox
  convert he using 1
  unfold uAmplitude
  push_cast
  ring
lemma vAmplitudeBox_contains {a : CBox} {n j : ℕ} (ha : a.Contains (basisAlpha n j)) :
    (vAmplitudeBox a).Contains (vAmplitude n j) := by
  have he := CBox.contains_mul (CBox.contains_scale piI_contains 2 1 (by norm_num)) ha
  unfold vAmplitudeBox
  convert he using 1
  unfold vAmplitude
  push_cast
  ring

-- Zero-based piece indexing: this is exactly the source M_1,...,M_6.
def densityNum : Fin 6 → ℤ := ![56,48,35,25,19,1571]
def densityDen : Fin 6 → ℤ := ![1,1,1,1,1,250]
noncomputable def densityCap (j : Fin 6) : ℝ := (densityNum j:ℝ)/(densityDen j:ℝ)
lemma densityDen_pos (j : Fin 6) : 0 < densityDen j := by fin_cases j <;> norm_num [densityDen]

def DensityCheck (n : ℕ) (j : Fin 6) : Prop :=
  (uAmplitudeBox (RBox.rat j.val 6) (aLookup n j) (bLookup n j)).SqNormCheck (densityNum j) (densityDen j) ∧
  (uAmplitudeBox (RBox.rat (j.val+1) 6) (aLookup n j) (bLookup n j)).SqNormCheck (densityNum j) (densityDen j) ∧
  (vAmplitudeBox (aLookup n j)).SqNormCheck (densityNum j) (densityDen j)
instance (n : ℕ) (j : Fin 6) : Decidable (DensityCheck n j) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

lemma density_finite_check (n : Fin 12) (hn : n.val ∈ residues) (j : Fin 6) : DensityCheck n.val j := by
  fin_cases n <;> simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  all_goals first | omega | (fin_cases j <;> decide +kernel)

lemma density_check (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) : DensityCheck n j := by
  have hc := density_finite_check ⟨n%12,by omega⟩ hn j
  simpa only [DensityCheck,aLookup,bLookup,Nat.mod_mod] using hc

lemma amplitude_endpoints (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) :
    ‖uAmplitude n j.val ((j.val:ℝ)/6)‖ ≤ densityCap j ∧
    ‖uAmplitude n j.val (((j.val:ℝ)+1)/6)‖ ≤ densityCap j ∧
    ‖vAmplitude n j.val‖ ≤ densityCap j := by
  obtain ⟨hc0,hc1,hcv⟩ := density_check n hn j
  have ha := aLookup_contains n j
  have hb := bLookup_contains n j
  refine ⟨?_,?_,CBox.norm_le_rat (vAmplitudeBox_contains ha) hcv⟩
  · exact CBox.norm_le_rat
      (uAmplitudeBox_contains (by simpa using RBox.contains_rat j.val 6 (by norm_num)) ha hb) hc0
  · exact CBox.norm_le_rat
      (uAmplitudeBox_contains (by simpa using RBox.contains_rat (j.val+1) 6 (by norm_num)) ha hb) hc1

lemma uAmplitude_bound (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) : ‖uAmplitude n j.val t‖ ≤ densityCap j := by
  obtain ⟨h0,h1,_⟩ := amplitude_endpoints n hn j
  let θ : ℝ := 6*t-j.val
  have hθ0 : 0 ≤ θ := by dsimp [θ]; linarith [ht.1]
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith [ht.2]
  have hid : uAmplitude n j.val t = ((1-θ:ℝ):ℂ)*uAmplitude n j.val ((j.val:ℝ)/6)+
      (θ:ℂ)*uAmplitude n j.val (((j.val:ℝ)+1)/6) := by
    unfold uAmplitude θ
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ ‖((1-θ:ℝ):ℂ)*uAmplitude n j.val ((j.val:ℝ)/6)‖+
        ‖(θ:ℂ)*uAmplitude n j.val (((j.val:ℝ)+1)/6)‖ := norm_add_le _ _
    _ = (1-θ)*‖uAmplitude n j.val ((j.val:ℝ)/6)‖+
        θ*‖uAmplitude n j.val (((j.val:ℝ)+1)/6)‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hθ0,
        abs_of_nonneg (sub_nonneg.mpr hθ1)]
    _ ≤ (1-θ)*densityCap j+θ*densityCap j := by gcongr
    _ = densityCap j := by ring

lemma unit_phase_norm (n : ℕ) (t : ℝ) : ‖Complex.exp (-Complex.I*Real.pi*t*n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp
lemma u_norm_amplitude (n j : ℕ) (t : ℝ) : ‖u n j t‖ = ‖uAmplitude n j t‖ := by
  rw [u_factored]
  have he : -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
      (basisBeta n j-(t:ℂ)*basisAlpha n j) = Complex.exp (-Complex.I*Real.pi*t*n)*uAmplitude n j t := by
    unfold uAmplitude; ring
  rw [he,norm_mul,unit_phase_norm,one_mul]
lemma v_norm_amplitude (n j : ℕ) (t : ℝ) : ‖v n j t‖ = ‖vAmplitude n j‖ := by
  rw [v_factored]
  have he : 2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n)*basisAlpha n j =
      Complex.exp (-Complex.I*Real.pi*t*n)*vAmplitude n j := by
    unfold vAmplitude; ring
  rw [he,norm_mul,unit_phase_norm,one_mul]


lemma basis_density_bounds (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖u n j.val t‖ ≤ densityCap j ∧ ‖v n j.val t‖ ≤ densityCap j := by
  rw [u_norm_amplitude,v_norm_amplitude]
  exact ⟨uAmplitude_bound n hn j ht,(amplitude_endpoints n hn j).2.2⟩

end SharpPlanar.IntegerBasis

namespace SharpPlanar
open IntegerBasis

lemma densityCap_nonneg (j : Fin 6) : 0 ≤ densityCap j := by
  fin_cases j <;> norm_num [densityCap,densityNum,densityDen]
lemma piece_summand_bound (x : X) (n : Node) (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖(x (n,false):ℂ)*u n.val j.val t+(x (n,true):ℂ)*v n.val j.val t‖ ≤
      densityCap j*(|x (n,false)|+|x (n,true)|) := by
  obtain ⟨hu,hv⟩ := basis_density_bounds n.val n.prop.2 j ht
  calc
    _ ≤ ‖(x (n,false):ℂ)*u n.val j.val t‖+‖(x (n,true):ℂ)*v n.val j.val t‖ := norm_add_le _ _
    _ = |x (n,false)| *‖u n.val j.val t‖+|x (n,true)| *‖v n.val j.val t‖ := by simp
    _ ≤ |x (n,false)| *densityCap j+|x (n,true)| *densityCap j := by gcongr
    _ = _ := by ring

lemma piece_density_bound (p : CardinalData) (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖density p j.val t‖ ≤ densityCap j*(|p.c₀|+|p.d₀|+‖p.x‖) := by
  have hnorm : Summable (fun n : Node => ‖(p.x (n,false):ℂ)*u n.val j.val t+
      (p.x (n,true):ℂ)*v n.val j.val t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => piece_summand_bound p.x n j ht)
      ((X_summable_pairs p.x).mul_left (densityCap j))
  have hsum : ‖∑' n : Node, ((p.x (n,false):ℂ)*u n.val j.val t+
      (p.x (n,true):ℂ)*v n.val j.val t)‖ ≤ densityCap j*‖p.x‖ := by
    calc
      _ ≤ ∑' n : Node, ‖(p.x (n,false):ℂ)*u n.val j.val t+
        (p.x (n,true):ℂ)*v n.val j.val t‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : Node, densityCap j*(|p.x (n,false)|+|p.x (n,true)|) :=
        hnorm.tsum_le_tsum (fun n => piece_summand_bound p.x n j ht)
          ((X_summable_pairs p.x).mul_left (densityCap j))
      _ = _ := by rw [tsum_mul_left,← X_norm]
  obtain ⟨hu,hv⟩ := basis_density_bounds 0 (by simp [residues]) j ht
  unfold density
  calc
    _ ≤ ‖(p.c₀:ℂ)*u 0 j.val t‖+‖(p.d₀:ℂ)*v 0 j.val t‖+
        ‖∑' n : Node, ((p.x (n,false):ℂ)*u n.val j.val t+
          (p.x (n,true):ℂ)*v n.val j.val t)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |p.c₀| *densityCap j+|p.d₀| *densityCap j+densityCap j*‖p.x‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      gcongr
    _ = _ := by ring

lemma lambdaCap_nonneg (j : Fin 7) : 0 ≤ lambdaCap j := by fin_cases j <;> norm_num [lambdaCap]
lemma zCap_nonneg (j : Fin 7) : 0 ≤ zCap j := by fin_cases j <;> norm_num [zCap]
lemma dampingCap_pos (j : Fin 7) : 0 < dampingCap j := by fin_cases j <;> norm_num [dampingCap]
lemma slopeCap_nonneg (j : Fin 6) : 0 ≤ slopeCap j := by fin_cases j <;> norm_num [slopeCap]

noncomputable def pieceMass (j : Fin 6) (s : ℝ) : ℝ :=
  if slopeCap j*s=0 then 1/6 else min (1/6) (1/(Real.pi*slopeCap j*s))
noncomputable def pieceL (j : Fin 6) (s : ℝ) : ℝ :=
  lambdaCap ⟨j.val,by omega⟩*Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*pieceMass j s
noncomputable def atomMass : Fin 7 → ℝ := ![5,4,4,4,2,4,2]
noncomputable def atomL (j : Fin 7) (s : ℝ) : ℝ :=
  atomMass j*lambdaCap j*Real.exp (-Real.pi*dampingCap j*s)
noncomputable def segmentEnvelope (j : Fin 6) (ell : ℕ) (s t : ℝ) : ℝ :=
  lambdaCap ⟨j.val,by omega⟩*(Real.pi*zCap ⟨j.val,by omega⟩)^ell *
    Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
    Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t))

lemma segmentEnvelope_nonneg (j : Fin 6) (ell : ℕ) (s t : ℝ) :
    0 ≤ segmentEnvelope j ell s t := by
  unfold segmentEnvelope
  exact mul_nonneg (mul_nonneg (mul_nonneg (lambdaCap_nonneg _)
    (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg _)) _)) (Real.exp_pos _).le) (Real.exp_pos _).le
lemma kernelMoment_segment_bound (j : Fin 6) (ell : ℕ) {s t : ℝ} (hs : 0 ≤ s)
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖kernelMoment ell s t‖ ≤ segmentEnvelope j ell s t := by
  obtain ⟨hl,hz,hi⟩ := piece_kernel_bounds j ht
  have hex : ‖Complex.exp (Complex.I*Real.pi*z t*s)‖ ≤
      Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
      Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t)) := by
    rw [← Real.exp_add,Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,zero_sub,
      sub_zero,zero_add]
    nlinarith [mul_le_mul_of_nonneg_right hi (mul_nonneg Real.pi_pos.le hs)]
  unfold kernelMoment segmentEnvelope
  rw [norm_mul,norm_mul,norm_pow,norm_mul,norm_mul,Complex.norm_I,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul]
  have hp : (Real.pi*‖z t‖)^ell ≤ (Real.pi*zCap ⟨j.val,by omega⟩)^ell := by
    gcongr
  calc
    _ ≤ lambdaCap ⟨j.val,by omega⟩*(Real.pi*zCap ⟨j.val,by omega⟩)^ell *
        (Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
         Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t))) :=
      mul_le_mul (mul_le_mul hl hp (by positivity) (lambdaCap_nonneg _)) hex
        (norm_nonneg _) (mul_nonneg (lambdaCap_nonneg _) (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg _)) _))
    _ = _ := by ring

lemma exp_segment_bound {a l u : ℝ} (ha : 0 ≤ a) (hlu : l ≤ u) :
    (∫ t in l..u, Real.exp (-a*(u-t))) ≤ if a=0 then u-l else min (u-l) (1/a) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-a*(u-t))) := by fun_prop
  have hcl : (∫ t in l..u, Real.exp (-a*(u-t))) ≤ u-l := by
    calc
      _ ≤ ∫ t in l..u, (1:ℝ) := by
        apply intervalIntegral.integral_mono_on hlu (hc.intervalIntegrable l u) (continuous_const.intervalIntegrable l u)
        intro t ht
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sub_nonneg.mpr ht.2)
      _ = u-l := by simp
  split_ifs with h0
  · exact hcl
  · apply le_min hcl
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    have hp : ∀ t ∈ Set.uIcc l u, HasDerivAt (fun t : ℝ => Real.exp (-a*(u-t))/a)
        (Real.exp (-a*(u-t))) t := by
      intro t _
      exact ((((hasDerivAt_id t).const_sub u).const_mul (-a)).exp.div_const a).congr_deriv (by simp [h0])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hp (hc.intervalIntegrable l u)]
    simp only [sub_self,mul_zero,Real.exp_zero]
    exact sub_le_self _ (div_nonneg (Real.exp_pos _).le ha)

lemma pieceMass_nonneg (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ pieceMass j s := by
  unfold pieceMass
  split_ifs
  · norm_num
  · exact le_min (by norm_num) (div_nonneg (by norm_num) (mul_nonneg (mul_nonneg Real.pi_pos.le (slopeCap_nonneg _)) hs))

lemma segment_exp_integral_bound (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) :
    (∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6,
      Real.exp (-(Real.pi*slopeCap j*s)*(((j.val:ℝ)+1)/6-t))) ≤ pieceMass j s := by
  have he := exp_segment_bound (mul_nonneg (mul_nonneg Real.pi_pos.le (slopeCap_nonneg j)) hs)
    (by linarith : (j.val:ℝ)/6 ≤ ((j.val:ℝ)+1)/6)
  have hlen : ((j.val:ℝ)+1)/6-(j.val:ℝ)/6=1/6 := by ring
  simpa only [pieceMass,hlen,mul_assoc,mul_eq_zero,Real.pi_ne_zero,false_or] using he

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

lemma segmentEnvelope_integral_bound (j : Fin 6) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, segmentEnvelope j ell s t) ≤
      pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell := by
  unfold segmentEnvelope
  rw [intervalIntegral.integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left (segment_exp_integral_bound j hs)
    (mul_nonneg (mul_nonneg (lambdaCap_nonneg ⟨j.val,by omega⟩)
      (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg ⟨j.val,by omega⟩)) ell))
      (Real.exp_pos (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)).le)
  convert hb using 1; first | rfl | (unfold pieceL; ring)

lemma sharp_integral_piece_bound (p : CardinalData) (j : Fin 6) (ell : ℕ) {s : ℝ}
    (hs : 0 ≤ s) :
    ‖∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, density p j.val t*kernelMoment ell s t‖ ≤
      (|p.c₀|+|p.d₀|+‖p.x‖)*densityCap j*pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell := by
  let w : ℝ := |p.c₀|+|p.d₀|+‖p.x‖
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hlu : (j.val:ℝ)/6 ≤ ((j.val:ℝ)+1)/6 := by linarith
  calc
    _ ≤ ∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, ‖density p j.val t*kernelMoment ell s t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hlu
    _ ≤ ∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, (w*densityCap j)*segmentEnvelope j ell s t := by
      apply intervalIntegral.integral_mono_on hlu (piece_integrable p ell j.val j.isLt s).norm
        ((by unfold segmentEnvelope; fun_prop : Continuous (fun t : ℝ => (w*densityCap j)*segmentEnvelope j ell s t)).intervalIntegrable _ _)
      intro t ht
      rw [norm_mul]
      have hd := piece_density_bound p j ht
      have hk := kernelMoment_segment_bound j ell hs ht
      rw [mul_comm w]
      exact mul_le_mul hd hk (norm_nonneg _) (mul_nonneg (densityCap_nonneg _) hw)
    _ = (w*densityCap j)*(∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, segmentEnvelope j ell s t) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (w*densityCap j)*(pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell) :=
      mul_le_mul_of_nonneg_left (segmentEnvelope_integral_bound j ell hs) (mul_nonneg hw (densityCap_nonneg _))
    _ = _ := by dsimp [w]; ring

lemma kernelMoment_endpoint_bound (j : Fin 7) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖kernelMoment ell s ((j.val:ℝ)/6)‖ ≤
      lambdaCap j*Real.exp (-Real.pi*dampingCap j*s)*(Real.pi*zCap j)^ell := by
  obtain ⟨hl,hz,hi⟩ := endpoint_kernel_bounds j
  have hex : ‖Complex.exp (Complex.I*Real.pi*z ((j.val:ℝ)/6)*s)‖ ≤
      Real.exp (-Real.pi*dampingCap j*s) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,zero_sub,
      sub_zero,zero_add]
    nlinarith [mul_le_mul_of_nonneg_right hi (mul_nonneg Real.pi_pos.le hs)]
  unfold kernelMoment
  rw [norm_mul,norm_mul,norm_pow,norm_mul,norm_mul,Complex.norm_I,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,one_mul]
  have hp : (Real.pi*‖z ((j.val:ℝ)/6)‖)^ell ≤ (Real.pi*zCap j)^ell := by gcongr
  calc
    _ ≤ lambdaCap j*(Real.pi*zCap j)^ell*Real.exp (-Real.pi*dampingCap j*s) :=
      mul_le_mul (mul_le_mul hl hp (by positivity) (lambdaCap_nonneg _)) hex
        (norm_nonneg _) (mul_nonneg (lambdaCap_nonneg _) (pow_nonneg (mul_nonneg Real.pi_pos.le (zCap_nonneg _)) _))
    _ = _ := by ring

noncomputable def atomicCoefficient (j : Fin 7) : ℂ := if j.val=0 then Pcoeff 0 else 2*Pcoeff j.val
lemma atomicCoefficient_norm (j : Fin 7) : ‖atomicCoefficient j‖ = atomMass j := by
  fin_cases j <;> norm_num [atomicCoefficient,atomMass,norm_mul,Pcoeff_norm,coeffMass]

lemma sharp_atomic_bound (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ‖Pcoeff 0*kernelMoment ell s 0+
      ∑ j ∈ Finset.Icc 1 6, 2*Pcoeff j*kernelMoment ell s ((j:ℝ)/6)‖ ≤
      ∑ j : Fin 7, atomL j s*(Real.pi*zCap j)^ell := by
  have he : Pcoeff 0*kernelMoment ell s 0+
      ∑ j ∈ Finset.Icc 1 6, 2*Pcoeff j*kernelMoment ell s ((j:ℝ)/6) =
      ∑ j : Fin 7, atomicCoefficient j*kernelMoment ell s ((j.val:ℝ)/6) := by
    norm_num [Fin.sum_univ_succ,Finset.sum_Icc_succ_top,atomicCoefficient]
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,atomicCoefficient_norm]
  have hh := mul_le_mul_of_nonneg_left (kernelMoment_endpoint_bound j ell hs)
    (by fin_cases j <;> norm_num [atomMass] : 0 ≤ atomMass j)
  convert hh using 1
  unfold atomL
  ring


theorem sharp_moment_bound (p : CardinalData) (ell : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |K p ell s| ≤
      (|p.c₀|+|p.d₀|+‖p.x‖)*(∑ j : Fin 6, densityCap j*pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell)
      +|p.C| *(∑ j : Fin 7, atomL j s*(Real.pi*zCap j)^ell) := by
  have hatom : ‖(p.C:ℂ)*(Pcoeff 0*kernelMoment ell s 0+
      ∑ j ∈ Finset.Icc 1 6, 2*Pcoeff j*kernelMoment ell s ((j:ℝ)/6))‖ ≤
      |p.C| *(∑ j : Fin 7, atomL j s*(Real.pi*zCap j)^ell) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (sharp_atomic_bound ell hs) (abs_nonneg _)
  have hsum : ‖∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density p j t*kernelMoment ell s t‖ ≤
      (|p.c₀|+|p.d₀|+‖p.x‖)*(∑ j : Fin 6, densityCap j*pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell) := by
    rw [← Fin.sum_univ_eq_sum_range,Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_assoc] using sharp_integral_piece_bound p j ell hs
  unfold K
  exact (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (by linarith))

end SharpPlanar

namespace SharpPlanar

lemma pieceMass_antitone (j : Fin 6) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    pieceMass j t ≤ pieceMass j s := by
  have ht : 0 ≤ t := hs.trans hst
  unfold pieceMass
  split_ifs with htz hsz hsz
  · rfl
  · exfalso
    have hz : slopeCap j*s=0 := by
      apply le_antisymm
      · calc
          _ ≤ slopeCap j*t := mul_le_mul_of_nonneg_left hst (slopeCap_nonneg _)
          _ = 0 := htz
      · exact mul_nonneg (slopeCap_nonneg _) hs
    exact hsz hz
  · exact min_le_left _ _
  · apply min_le_min_left
    apply one_div_le_one_div_of_le
    · have hh : 0 < slopeCap j*s := lt_of_le_of_ne (mul_nonneg (slopeCap_nonneg _) hs) (Ne.symm hsz)
      simpa only [mul_assoc] using mul_pos Real.pi_pos hh
    · exact mul_le_mul_of_nonneg_left hst (mul_nonneg Real.pi_pos.le (slopeCap_nonneg _))

lemma pieceL_nonneg (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ pieceL j s := by
  exact mul_nonneg (mul_nonneg (lambdaCap_nonneg _) (Real.exp_pos _).le) (pieceMass_nonneg j hs)
lemma atomL_nonneg (j : Fin 7) (s : ℝ) : 0 ≤ atomL j s := by
  unfold atomL
  apply mul_nonneg _ (Real.exp_pos _).le
  apply mul_nonneg _ (lambdaCap_nonneg _)
  fin_cases j <;> norm_num [atomMass]

lemma pieceL_shift_bound (j : Fin 6) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    pieceL j (s+t) ≤ Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*t)*pieceL j s := by
  have hm := pieceMass_antitone j hs (show s ≤ s+t by linarith)
  unfold pieceL
  rw [mul_add,Real.exp_add]
  calc
    _ ≤ lambdaCap ⟨j.val,by omega⟩*(Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*
        Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*t))*pieceMass j s := by
      exact mul_le_mul_of_nonneg_left hm (mul_nonneg (lambdaCap_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    _ = _ := by ring

lemma atomL_shift (j : Fin 7) (s t : ℝ) :
    atomL j (s+t) = Real.exp (-Real.pi*dampingCap j*t)*atomL j s := by
  unfold atomL
  rw [mul_add,Real.exp_add]
  ring

lemma pieceL_period_bound (j : Fin 6) {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    pieceL j (s+12*k) ≤ (Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))^k*pieceL j s := by
  have hh := pieceL_shift_bound j hs (by positivity : (0:ℝ) ≤ 12*k)
  convert hh using 1
  rw [← Real.exp_nat_mul]
  congr 2
  ring

end SharpPlanar

namespace SharpPlanar
open IntegerBasis


lemma periodic_geometric_sum {f : ℕ → ℝ} {q : ℝ} (hf : ∀ n, 0 ≤ f n)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ (a : Fin 12) (k : ℕ), f (k*12+a.val) ≤ q^k*f a.val) :
    Summable f ∧ (∑' n, f n) ≤ (∑ a : Fin 12, f a.val)/(1-q) := by
  let g : ℕ × Fin 12 → ℝ := fun p => q^p.1*f p.2.val
  have hgeom := (hasSum_geometric_of_lt_one hq0 hq1).summable
  have hg : Summable g := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (pow_nonneg hq0 _) (hf _))).mpr
    constructor
    · intro k; exact summable_of_hasFiniteSupport (Set.toFinite _)
    · simpa only [g,← Finset.mul_sum,tsum_fintype] using hgeom.mul_right (∑ a : Fin 12, f a.val)
  have hh : Summable (fun p : ℕ × Fin 12 => f (p.1*12+p.2.val)) :=
    Summable.of_nonneg_of_le (fun _ => hf _) (fun p => hb p.2 p.1) hg
  have heq : (fun p : ℕ × Fin 12 => f (p.1*12+p.2.val)) = f ∘ (Nat.divModEquiv 12).symm := rfl
  have hs : Summable f := ((Nat.divModEquiv 12).symm.summable_iff).mp (heq ▸ hh)
  refine ⟨hs,?_⟩
  calc
    (∑' n, f n) = ∑' p : ℕ × Fin 12, f (p.1*12+p.2.val) := by
      exact ((Nat.divModEquiv 12).symm.tsum_eq f).symm
    _ ≤ ∑' p : ℕ × Fin 12, g p := hh.tsum_le_tsum (fun p => hb p.2 p.1) hg
    _ = (∑ a : Fin 12, f a.val)/(1-q) := by
      rw [hg.tsum_prod]
      simp only [g,tsum_fintype,← Finset.mul_sum,tsum_mul_right]
      rw [tsum_geometric_of_lt_one hq0 hq1]
      rw [div_eq_mul_inv]
      ring

noncomputable def rowFactor (j : Fin 6) (n : ℕ) : ℝ :=
  (1+|D n|+Real.pi*zCap ⟨j.val,by omega⟩)/Q n*densityCap j
noncomputable def rowPiece (j : Fin 6) (n : ℕ) : ℝ :=
  if n%12 ∈ residues then rowFactor j n * pieceL j n else 0
noncomputable def rowTable (N : ℕ) : ℝ :=
  ∑ j : Fin 6, (∑ a : Fin 12, rowPiece j (N+1+a.val)) /
    (1-Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))

lemma rowFactor_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ rowFactor j n := by
  unfold rowFactor
  exact mul_nonneg (div_nonneg (by have hz := zCap_nonneg (⟨j.val,by omega⟩ : Fin 7); positivity) (Q_pos _).le) (densityCap_nonneg _)
lemma rowFactor_periodic (j : Fin 6) (n k : ℕ) : rowFactor j (n+12*k) = rowFactor j n := by
  have hmod : (n+12*k)%12 = n%12 := by omega
  unfold rowFactor Q D
  rw [hmod]
lemma rowPiece_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ rowPiece j n := by
  unfold rowPiece
  split_ifs
  · exact mul_nonneg (rowFactor_nonneg _ _) (pieceL_nonneg _ (Nat.cast_nonneg _))
  · rfl
lemma rowPiece_period_bound (j : Fin 6) (n k : ℕ) :
    rowPiece j (n+12*k) ≤ (Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))^k*rowPiece j n := by
  have hmod : (n+12*k)%12 = n%12 := by omega
  unfold rowPiece
  rw [hmod]
  split_ifs with hn
  · rw [rowFactor_periodic]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    calc
      _ ≤ rowFactor j n*((Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩))^k*pieceL j n) :=
        mul_le_mul_of_nonneg_left (pieceL_period_bound j (Nat.cast_nonneg _) k) (rowFactor_nonneg _ _)
      _ = _ := by ring
  · simp

lemma rowPiece_tail_sum (j : Fin 6) (N : ℕ) :
    Summable (fun n : ℕ => rowPiece j (N+1+n)) ∧
    (∑' n : ℕ, rowPiece j (N+1+n)) ≤
      (∑ a : Fin 12, rowPiece j (N+1+a.val)) /
        (1-Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩)) := by
  apply periodic_geometric_sum (fun _ => rowPiece_nonneg j _) (Real.exp_pos _).le
  · apply Real.exp_lt_one_iff.mpr
    have hg := dampingCap_pos (⟨j.val+1,by omega⟩ : Fin 7)
    nlinarith [Real.pi_pos,mul_pos Real.pi_pos hg]
  · intro a k
    convert rowPiece_period_bound j (N+1+a.val) k using 1
    congr 1
    omega

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

lemma paired_jet_bound {q : ℝ} (hq : 0 < q) (d a b : ℝ) :
    |-a/q|+|(d*a-b)/q| ≤ ((1+|d|)*|a|+|b|)/q := by
  rw [abs_div,abs_div,abs_neg,abs_of_pos hq,← add_div]
  apply div_le_div_of_nonneg_right _ hq.le
  have hh := abs_sub (d*a) b
  rw [abs_mul] at hh
  nlinarith

lemma sharp_S_row (x : X) (n : Node) :
    |S x (n,false)|+|S x (n,true)| ≤ ‖x‖*(∑ j : Fin 6, rowPiece j n.val) := by
  have hs : (0:ℝ) ≤ n.val := Nat.cast_nonneg _
  have h0 := sharp_moment_bound (positiveData x) 0 hs
  have h1 := sharp_moment_bound (positiveData x) 1 hs
  simp only [positiveData,abs_zero,zero_add,zero_mul,add_zero,pow_zero,mul_one] at h0
  simp only [positiveData,abs_zero,zero_add,zero_mul,add_zero,pow_one] at h1
  have hq := Q_pos n.val
  rw [S_apply,S_apply]
  simp only [Scoords,Bool.false_eq_true,ite_false,ite_true]
  calc
    _ ≤ ((1+|D n.val|)*|K (positiveData x) 0 n.val|+|K (positiveData x) 1 n.val|)/Q n.val :=
      paired_jet_bound hq _ _ _
    _ ≤ ((1+|D n.val|)*(‖x‖*(∑ j : Fin 6, densityCap j*pieceL j n.val))+
      ‖x‖*(∑ j : Fin 6, densityCap j*pieceL j n.val*(Real.pi*zCap ⟨j.val,by omega⟩)))/Q n.val := by
      exact div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left h0 (by positivity)) h1) hq.le
    _ = _ := by
      simp only [rowPiece,n.prop.2,ite_true,rowFactor,div_eq_mul_inv]
      rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

noncomputable def rowTailNorm (x : X) (N : ℕ) : ℝ :=
  ∑' n : {n : Node // N<n.val}, (|x (n.val,false)|+|x (n.val,true)|)

lemma rowTailNorm_summable (x : X) (N : ℕ) :
    Summable (fun n : {n : Node // N<n.val} => |x (n.val,false)|+|x (n.val,true)|) := by
  exact (X_summable_pairs x).subtype _

lemma natural_row_tail_summable (N : ℕ) :
    Summable (fun k : ℕ => ∑ j : Fin 6, rowPiece j (N+1+k)) := by
  exact (hasSum_sum (fun j _ => (rowPiece_tail_sum j N).1.hasSum)).summable

lemma natural_row_tail_bound (N : ℕ) :
    (∑' k : ℕ, ∑ j : Fin 6, rowPiece j (N+1+k)) ≤ rowTable N := by
  rw [Summable.tsum_finsetSum (fun j _ => (rowPiece_tail_sum j N).1)]
  exact Finset.sum_le_sum (fun j _ => (rowPiece_tail_sum j N).2)


theorem sharp_S_tail (x : X) (N : ℕ) : rowTailNorm (S x) N ≤ rowTable N*‖x‖ := by
  let f : ℕ → ℝ := fun k => ∑ j : Fin 6, rowPiece j (N+1+k)
  let index : {n : Node // N<n.val} → ℕ := fun n => n.val.val-(N+1)
  have hi : Function.Injective index := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have ha := a.prop; have hb := b.prop
    dsimp only [index] at hab
    omega
  have he (n : {n : Node // N<n.val}) : N+1+index n=n.val.val := by
    have hn := n.prop
    dsimp only [index]
    omega
  have hf : Summable f := natural_row_tail_summable N
  have hfn : ∀ n, 0 ≤ f n := fun n => Finset.sum_nonneg (fun _ _ => rowPiece_nonneg _ _)
  have hfi : Summable (f ∘ index) := hf.comp_injective hi
  have hsum : (∑' n, f (index n)) ≤ rowTable N :=
    (tsum_comp_le_tsum_of_inj hf hfn hi).trans (natural_row_tail_bound N)
  calc
    rowTailNorm (S x) N ≤ ∑' n : {n : Node // N<n.val}, ‖x‖*f (index n) := by
      apply (rowTailNorm_summable (S x) N).tsum_le_tsum _ (hfi.mul_left ‖x‖)
      intro n
      simpa only [Function.comp_apply, f, he] using sharp_S_row x n.val
    _ = ‖x‖*(∑' n, f (index n)) := tsum_mul_left
    _ ≤ ‖x‖*rowTable N := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = rowTable N*‖x‖ := mul_comm _ _

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

noncomputable def rowQLower (n : ℕ) : ℝ :=
  if n%12=0 ∨ n%12=4 then 32898/10000 else
  if n%12=1 ∨ n%12=3 then 17629/10000 else 24555/1000
noncomputable def rowDUpper (n : ℕ) : ℝ :=
  if n%12=0 ∨ n%12=4 then 21162/10000 else
  if n%12=1 ∨ n%12=3 then 8260/10000 else 2214/10000

lemma pi_fine : (314159/100000:ℝ) < Real.pi ∧ Real.pi < 31416/10000 := by
  constructor <;> linarith [Real.pi_gt_d6,Real.pi_lt_d6]
lemma b_fine : (86602/100000:ℝ) < b ∧ b < 86603/100000 := by
  constructor <;> nlinarith [b_pos,b_sq]

lemma rowQLower_bound (n : ℕ) (hn : n%12 ∈ residues) : 0 < rowQLower n ∧ rowQLower n < Q n := by
  have hp := pi_fine
  have hb := b_fine
  have hp2 : (314159/100000:ℝ)^2 < Real.pi^2 := by nlinarith [Real.pi_pos]
  have hsmall : (2*(314159/100000:ℝ)^2/3)*(2-2*(86603/100000)) < (2*Real.pi^2/3)*(2-2*b) := by
    gcongr; linarith
  have hlarge : (2*(314159/100000:ℝ)^2/3)*(2+2*(86602/100000)) < (2*Real.pi^2/3)*(2+2*b) := by
    gcongr; linarith
  rw [← Q_mod]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;>
    simp [rowQLower,hn,Q_0,Q_1,Q_3,Q_4,Q_7,Q_9] <;> nlinarith

lemma rowDUpper_bound (n : ℕ) (hn : n%12 ∈ residues) : |D n| < rowDUpper n := by
  have hp := pi_fine
  have hb := b_fine
  have hpb : Real.pi*b < (31416/10000:ℝ)*(86603/100000) := by gcongr <;> linarith
  have hpb0 : (314159/100000:ℝ)*(86602/100000) < Real.pi*b := by gcongr <;> linarith
  have hpbpos : 0 < Real.pi*b := mul_pos Real.pi_pos b_pos
  rw [← D_mod]
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;>
    norm_num [rowDUpper,hn]
  all_goals first | rw [D_0] | rw [D_1] | rw [D_3] | rw [D_4] | rw [D_7] | rw [D_9]
  all_goals apply abs_lt.mpr; constructor <;> nlinarith

end SharpPlanar

namespace SharpPlanar
open IntegerBasis
noncomputable def pieceBase : Fin 6 → ℝ := ![469/1000000,7279/1000000,59165/1000000,219974/1000000,494744/1000000,828986/1000000]
lemma pieceBase_pos (j : Fin 6) : 0 < pieceBase j := by fin_cases j <;> norm_num [pieceBase]
lemma pieceBase_lt_one (j : Fin 6) : pieceBase j < 1 := by fin_cases j <;> norm_num [pieceBase]
lemma pieceBase_contains (j : Fin 6) :
    Real.exp (-(314159/100000:ℝ)*dampingCap ⟨j.val+1,by omega⟩) ≤ pieceBase j := by
  have hg : 0 ≤ (314159/100000:ℝ)*dampingCap ⟨j.val+1,by omega⟩ := by
    exact mul_nonneg (by norm_num) (dampingCap_pos _).le
  have hp := Real.sum_le_exp_of_nonneg hg 20
  rw [neg_mul,Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
  have ht : 1 ≤ pieceBase j * (∑ i ∈ Finset.range 20,
      ((314159/100000:ℝ)*dampingCap ⟨j.val+1,by omega⟩)^i/(i.factorial:ℝ)) := by
    fin_cases j <;> norm_num [pieceBase,dampingCap,Finset.sum_range_succ]
  exact ht.trans (mul_le_mul_of_nonneg_left hp (pieceBase_pos j).le)

lemma decay_pieceBase (j : Fin 6) (n : ℕ) :
    Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*n) ≤ pieceBase j^n := by
  have he : Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩) ≤ pieceBase j :=
    (Real.exp_le_exp.mpr (by nlinarith [pi_fine,(dampingCap_pos ⟨j.val+1,by omega⟩)])).trans
      (pieceBase_contains j)
  rw [mul_comm _ (n:ℝ),Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le he n

noncomputable def massRational (j : Fin 6) (n : ℕ) : ℝ :=
  if slopeCap j*(n:ℝ)=0 then 1/6 else min (1/6) (1/((314159/100000:ℝ)*slopeCap j*n))
lemma massRational_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ massRational j n := by
  have hs := slopeCap_nonneg j
  unfold massRational
  split_ifs <;> positivity
lemma pieceMass_le (j : Fin 6) (n : ℕ) : pieceMass j n ≤ massRational j n := by
  unfold pieceMass massRational
  split_ifs with hz
  · rfl
  · apply min_le_min_left
    have hpos : 0 < slopeCap j*(n:ℝ) := lt_of_le_of_ne (mul_nonneg (slopeCap_nonneg j) (Nat.cast_nonneg n)) (Ne.symm hz)
    apply one_div_le_one_div_of_le
    · nlinarith
    · nlinarith [pi_fine]

noncomputable def factorRational (j : Fin 6) (n : ℕ) : ℝ :=
  (1+rowDUpper n+(31416/10000:ℝ)*zCap ⟨j.val,by omega⟩)/rowQLower n*densityCap j
noncomputable def pieceRational (j : Fin 6) (n : ℕ) : ℝ :=
  if n%12 ∈ residues then factorRational j n *
    (lambdaCap ⟨j.val,by omega⟩*pieceBase j^n*massRational j n) else 0
noncomputable def tableRational (N : ℕ) : ℝ :=
  ∑ j : Fin 6, (∑ a : Fin 12, pieceRational j (N+1+a.val))/(1-pieceBase j^12)
lemma factorRational_nonneg (j : Fin 6) (n : ℕ) : 0 ≤ factorRational j n := by
  have hq : 0 ≤ rowQLower n := by unfold rowQLower; split_ifs <;> norm_num
  have hd : 0 ≤ rowDUpper n := by unfold rowDUpper; split_ifs <;> norm_num
  have hz := zCap_nonneg ⟨j.val,by omega⟩
  unfold factorRational
  exact mul_nonneg (div_nonneg (by positivity) hq) (densityCap_nonneg j)
lemma rowFactor_le (j : Fin 6) (n : ℕ) (hn : n%12 ∈ residues) :
    rowFactor j n ≤ factorRational j n := by
  unfold rowFactor factorRational
  have hq := rowQLower_bound n hn
  have hd := rowDUpper_bound n hn
  have hz := zCap_nonneg ⟨j.val,by omega⟩
  apply mul_le_mul_of_nonneg_right _ (densityCap_nonneg j)
  have hd0 : 0 ≤ rowDUpper n := (abs_nonneg (D n)).trans hd.le
  apply div_le_div₀ (by positivity)
  · exact add_le_add (add_le_add le_rfl hd.le) (mul_le_mul_of_nonneg_right pi_fine.2.le hz)
  · exact hq.1
  · exact hq.2.le
lemma rowPiece_le (j : Fin 6) (n : ℕ) : rowPiece j n ≤ pieceRational j n := by
  unfold rowPiece pieceRational
  split_ifs with hn
  · unfold pieceL
    apply mul_le_mul (rowFactor_le j n hn)
    · apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (decay_pieceBase j n) (lambdaCap_nonneg _)
      · exact pieceMass_le j n
      · exact pieceMass_nonneg j (Nat.cast_nonneg n)
      · exact mul_nonneg (lambdaCap_nonneg _) (pow_nonneg (pieceBase_pos j).le _)
    · exact pieceL_nonneg j (Nat.cast_nonneg n)
    · exact factorRational_nonneg j n
  · rfl
lemma rowTable_le (N : ℕ) : rowTable N ≤ tableRational N := by
  unfold rowTable tableRational
  apply Finset.sum_le_sum
  intro j _
  have hd : 0 < 1-pieceBase j^12 := sub_pos.mpr (pow_lt_one₀ (pieceBase_pos j).le (pieceBase_lt_one j) (by norm_num))
  apply div_le_div₀
  · exact Finset.sum_nonneg (fun a _ => (rowPiece_nonneg j _).trans (rowPiece_le j _))
  · exact Finset.sum_le_sum (fun a _ => rowPiece_le j _)
  · exact hd
  · have he := decay_pieceBase j 12
    have heq : Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*(12:ℕ)) = Real.exp (-12*Real.pi*dampingCap ⟨j.val+1,by omega⟩) := by congr 1; push_cast; ring
    rw [heq] at he
    exact sub_le_sub_left he 1

lemma tableRational_zero : tableRational 0 < 28 := by
  norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase,
    rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap,
    residues,Fin.sum_univ_succ]
lemma tableRational_four : tableRational 4 < 28/100 := by
  norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase,
    rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap,
    residues,Fin.sum_univ_succ]
lemma tableRational_sixteen : tableRational 16 < 15/1000 := by
  norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase,
    rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap,
    residues,Fin.sum_univ_succ]
lemma tableRational_hundred : tableRational 100 < 5/10^10 := by
  norm_num [tableRational,pieceRational,factorRational,massRational,pieceBase,
    rowDUpper,rowQLower,lambdaCap,zCap,densityCap,densityNum,densityDen,slopeCap,
    residues,Fin.sum_univ_succ]

theorem rowTable_bounds : rowTable 0 < 28 ∧ rowTable 4 < 28/100 ∧
    rowTable 16 < 15/1000 ∧ rowTable 100 < 5/10^10 :=
  ⟨(rowTable_le 0).trans_lt tableRational_zero,(rowTable_le 4).trans_lt tableRational_four,
    (rowTable_le 16).trans_lt tableRational_sixteen,(rowTable_le 100).trans_lt tableRational_hundred⟩
end SharpPlanar

end OAI
