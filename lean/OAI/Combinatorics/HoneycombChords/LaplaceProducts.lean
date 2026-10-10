import OAI.Combinatorics.HoneycombChords.ObliqueProjection

namespace OAI

/-! Euler products and positive rational approximants of the strip test functions.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section


namespace CriticalHoneycomb.FiniteFunctional
open Finset Filter Topology

lemma prod_range_even_odd {R : Type*} [CommMonoid R] (f : ℕ → R) (n : ℕ) :
    (∏ j ∈ range (2*n), f j) = (∏ j ∈ range n,f (2*j))*(∏ j ∈ range n,f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,prod_range_succ,prod_range_succ,ih,
      prod_range_succ,prod_range_succ]
    ac_rfl

noncomputable def cosineEulerProduct (z : ℂ) (n : ℕ) : ℂ :=
  ∏ j ∈ range n,(1-4*z^2/((Real.pi:ℂ)^2*(2*(j:ℂ)+1)^2))

lemma cosineEulerProduct_relation (z : ℂ) (n : ℕ) :
    (∏ j ∈ range (2*n),((1:ℂ)-(2*z/(Real.pi:ℂ))^2/((j:ℂ)+1)^2)) =
      cosineEulerProduct z n * (∏ j ∈ range n,((1:ℂ)-(z/(Real.pi:ℂ))^2/((j:ℂ)+1)^2)) := by
  rw [prod_range_even_odd]
  apply congrArg₂ (·*·)
  · unfold cosineEulerProduct
    apply prod_congr rfl
    intro j hj
    push_cast
    have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hj : 2*(j:ℂ)+1≠0 := by exact_mod_cast (show (2*j+1:ℕ)≠0 by omega)
    field_simp [hp,hj]
    ring
  · apply prod_congr rfl
    intro j hj
    push_cast
    have hj : (j:ℂ)+1≠0 := Nat.cast_add_one_ne_zero j
    have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hk : 2*(j:ℂ)+1+1≠0 := by exact_mod_cast (show (2*j+1+1:ℕ)≠0 by omega)
    field_simp [hp,hj,hk]
    ring

lemma tendsto_cosineEulerProduct {z : ℂ} (hz : Complex.sin z ≠ 0) :
    Tendsto (cosineEulerProduct z) atTop (𝓝 (Complex.cos z)) := by
  have hz0 : z≠0 := by intro h;apply hz;simp [h]
  have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h₁ := Complex.tendsto_euler_sin_prod (z/(Real.pi:ℂ))
  have h₂ := (Complex.tendsto_euler_sin_prod (2*z/(Real.pi:ℂ))).comp
    (tendsto_id.const_mul_atTop' (by norm_num : (0:ℕ)<2))
  have he₁ : (Real.pi:ℂ)*(z/(Real.pi:ℂ))=z := by field_simp
  have he₂ : (Real.pi:ℂ)*(2*z/(Real.pi:ℂ))=2*z := by field_simp
  simp only [he₁] at h₁
  simp only [Function.comp_def,he₂] at h₂
  have hd := h₂.div (h₁.const_mul 2) (mul_ne_zero (by norm_num) hz)
  have he : Complex.sin (2*z)/(2*Complex.sin z)=Complex.cos z := by
    rw [Complex.sin_two_mul]
    field_simp
  rw [he] at hd
  apply hd.congr'
  filter_upwards [h₁.eventually (eventually_ne_nhds hz)] with n hn
  dsimp only [Pi.div_apply,id_eq]
  rw [cosineEulerProduct_relation]
  apply (div_eq_iff (mul_ne_zero (by norm_num) hn)).mpr
  ring

noncomputable def cEulerProduct (t x : ℝ) (n : ℕ) : ℂ :=
  ∏ j ∈ range n,(1+4*(t:ℂ)^2*(x:ℂ)/((Real.pi:ℂ)^2*(2*(j:ℂ)+1)^2))

lemma cEulerProduct_eq_cosineEulerProduct {t x : ℝ} {z : ℂ}
    (hz : z^2= -(t:ℂ)^2*(x:ℂ)) (n : ℕ) :
    cEulerProduct t x n=cosineEulerProduct z n := by
  unfold cEulerProduct cosineEulerProduct
  apply prod_congr rfl
  intro j hj
  rw [hz]
  ring

lemma tendsto_cEulerProduct {t x : ℝ} (ht : 0<t)
    (hx : 4*t^2*(-x)<Real.pi^2) :
    Tendsto (cEulerProduct t x) atTop (𝓝 (C t x)) := by
  rcases lt_trichotomy x 0 with hxneg|rfl|hxpos
  · let y:=t*Real.sqrt (-x)
    have hy : 0<y := mul_pos ht (Real.sqrt_pos.mpr (neg_pos.mpr hxneg))
    have hy2 : y^2=t^2*(-x) := by dsimp [y];rw [mul_pow,Real.sq_sqrt (neg_nonneg.mpr hxneg.le)]
    have hylt : y<Real.pi := by nlinarith [Real.pi_pos]
    have hs : Complex.sin (y:ℂ)≠0 := by
      rw [←Complex.ofReal_sin]
      exact Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hy hylt).ne'
    have hz : (y:ℂ)^2= -(t:ℂ)^2*(x:ℂ) := by
      have he : (y:ℂ)^2=(t:ℂ)^2*(-(x:ℂ)) := by exact_mod_cast hy2
      rw [he]
      ring
    have he : cEulerProduct t x=cosineEulerProduct (y:ℂ) :=
      funext (cEulerProduct_eq_cosineEulerProduct hz)
    rw [he]
    convert tendsto_cosineEulerProduct hs using 1
    simp only [C,ite_eq_right (not_le.mpr hxneg),Complex.ofReal_cos,y]
  · have he : cEulerProduct t 0=fun _=>1 := by ext n;simp [cEulerProduct]
    rw [he,C_zero]
    exact tendsto_const_nhds
  · let y:=t*Real.sqrt x
    have hy : 0<y := mul_pos ht (Real.sqrt_pos.mpr hxpos)
    have hy2 : y^2=t^2*x := by dsimp [y];rw [mul_pow,Real.sq_sqrt hxpos.le]
    have hs : Complex.sin ((y:ℂ)*Complex.I)≠0 := by
      rw [Complex.sin_mul_I]
      apply mul_ne_zero
      · rw [←Complex.ofReal_sinh]
        exact Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hy).ne'
      · exact Complex.I_ne_zero
    have hz : ((y:ℂ)*Complex.I)^2= -(t:ℂ)^2*(x:ℂ) := by
      rw [mul_pow,Complex.I_sq]
      have hy2' : (y:ℂ)^2=(t:ℂ)^2*(x:ℂ) := by exact_mod_cast hy2
      rw [hy2']
      ring
    rw [show cEulerProduct t x=cosineEulerProduct ((y:ℂ)*Complex.I) from
      funext (cEulerProduct_eq_cosineEulerProduct hz)]
    convert tendsto_cosineEulerProduct hs using 1
    simp only [C,ite_eq_left hxpos.le,Complex.cos_mul_I,Complex.ofReal_cosh,y]

end CriticalHoneycomb.FiniteFunctional

end


section


namespace CriticalHoneycomb.FiniteFunctional
open Finset MeasureTheory
open Analytic

lemma restrict_admissibleDensity {N : ℕ} {F : ℝ → ℂ} (hF : F ∈ admissibleDensity N) :
    ∃ f ∈ zDensity angle N,RepresentsDensity F f := by
  rw [← gBasis_span] at hF
  have hM {F : ℝ → ℂ} (hF : F ∈ M N) : ∃ f ∈ zDensity angle N,RepresentsDensity F f := by
    induction hF using Submodule.span_induction with
    | mem F hF =>
      rcases hF with (⟨j,rfl⟩|⟨j,rfl⟩)
      · refine ⟨zMonomial j,Submodule.subset_span (Or.inl (Or.inl ⟨j,rfl⟩)),?_⟩
        intro z hz
        simp only [zMonomial,Complex.ofReal_pow]
      · refine ⟨zCoshJet angle j,Submodule.subset_span (Or.inl (Or.inr ⟨j,rfl⟩)),?_⟩
        intro z hz
        exact C_sq_jet j angle hz.le
    | zero => exact ⟨0,(zDensity angle N).zero_mem,fun _ _=>rfl⟩
    | add F G hF hG hiF hiG =>
      obtain ⟨f,hf,hrep⟩ := hiF
      obtain ⟨g,hg,hrep'⟩ := hiG
      exact ⟨f+g,(zDensity angle N).add_mem hf hg,fun z hz=>congrArg₂ (·+·) (hrep z hz) (hrep' z hz)⟩
    | smul a F hF hiF =>
      obtain ⟨f,hf,hrep⟩ := hiF
      exact ⟨a • f,(zDensity angle N).smul_mem a hf,fun z hz=>congrArg (a • ·) (hrep z hz)⟩
  rw [gBasis_span] at hF
  obtain ⟨F₀,h₀,F₁,h₁,rfl⟩ := Submodule.mem_sup.mp hF
  obtain ⟨f,hf,hrep⟩ := hM h₀
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp h₁
  refine ⟨f+a • zG angle,(zDensity angle N).add_mem hf
    ((zDensity angle N).smul_mem a (Submodule.subset_span (Or.inr rfl))),?_⟩
  intro z hz
  simp only [Pi.add_apply,Pi.smul_apply]
  rw [hrep z hz,g_sq hz]
  rfl

lemma C_in_pairingDomain (N : ℕ) (u : ℝ) (hu : 2*angle+|u|<Real.pi/2) :
    InPairingDomain N (C u) := by
  intro j
  have hg : gBasis N j ∈ admissibleDensity N := by
    rw [←gBasis_span]
    exact Submodule.subset_span ⟨j,rfl⟩
  obtain ⟨f,hf,hrep⟩ := restrict_admissibleDensity hg
  simpa only [iteratedDeriv_zero] using pairingJet_integrable hrep hf 0 u hu

lemma div_D_in_pairingDomain (N : ℕ) (u : ℝ) (hu : angle+|u|<Real.pi/2) :
    InPairingDomain N (fun x=>C u x/D x) := by
  intro j
  have hg : gBasis N j ∈ admissibleDensity N := by
    rw [←gBasis_span]
    exact Submodule.subset_span ⟨j,rfl⟩
  obtain ⟨f,hf,hrep⟩ := restrict_admissibleDensity hg
  exact pairing_div_D_integrable hrep hf u hu

noncomputable def hZero (x : ℝ) : ℂ := (D x)⁻¹
noncomputable def hOne (x : ℝ) : ℂ := C (angle/2) x/D x
noncomputable def cThreeCorrection : ℝ → ℂ := C (3*angle/2)-hOne

lemma hZero_in_pairingDomain (N : ℕ) : InPairingDomain N hZero := by
  have h := div_D_in_pairingDomain N 0 (by rw [abs_zero,add_zero];exact angle_lt_pi_half)
  change InPairingDomain N (fun x => (D x)⁻¹)
  simpa only [C_parameter_zero,one_div] using h
lemma hOne_in_pairingDomain (N : ℕ) : InPairingDomain N hOne := by
  apply div_D_in_pairingDomain
  rw [abs_of_pos (half_pos angle_pos)]
  unfold angle
  linarith [Real.pi_pos]
lemma cThree_in_pairingDomain (N : ℕ) : InPairingDomain N (C (3*angle/2)) := by
  apply C_in_pairingDomain
  rw [abs_of_pos (by have := angle_pos;positivity : 0<3*angle/2)]
  unfold angle
  linarith [Real.pi_pos]
lemma cThreeCorrection_in_pairingDomain (N : ℕ) : InPairingDomain N cThreeCorrection :=
  fun j=>(cThree_in_pairingDomain N j).sub (hOne_in_pairingDomain N j)

end CriticalHoneycomb.FiniteFunctional

end


section


namespace CriticalHoneycomb.FiniteFunctional
open Finset Filter Topology

lemma C_re_pos {t x : ℝ} (ht : 0<t) (hx : 4*t^2*(-x)<Real.pi^2) : 0<(C t x).re := by
  unfold C
  split_ifs with h
  · simpa only [←Complex.ofReal_mul,←Complex.ofReal_cosh,Complex.ofReal_re] using Real.cosh_pos (t*Real.sqrt x)
  · have hn : 0≤-x := by linarith
    have hs : (t*Real.sqrt (-x))^2=t^2*(-x) := by rw [mul_pow,Real.sq_sqrt hn]
    have hy : 0≤t*Real.sqrt (-x) := mul_nonneg ht.le (Real.sqrt_nonneg _)
    have hp : t*Real.sqrt (-x)<Real.pi/2 := by nlinarith [Real.pi_pos]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hp⟩

lemma C_two_mul (t x : ℝ) : C (2*t) x=2*C t x^2-1 := by
  unfold C
  split_ifs
  · rw [show 2*t*Real.sqrt x=2*(t*Real.sqrt x) by ring,Real.cosh_two_mul,Real.sinh_sq]
    push_cast
    ring
  · rw [show 2*t*Real.sqrt (-x)=2*(t*Real.sqrt (-x)) by ring,Real.cos_two_mul]
    push_cast
    ring

lemma C_three_mul (t x : ℝ) : C (3*t) x=4*C t x^3-3*C t x := by
  unfold C
  split_ifs
  · rw [show 3*t*Real.sqrt x=3*(t*Real.sqrt x) by ring,Real.cosh_three_mul]
    push_cast
    ring
  · rw [show 3*t*Real.sqrt (-x)=3*(t*Real.sqrt (-x)) by ring,Real.cos_three_mul]
    push_cast
    ring

lemma D_mul_cOne (x : ℝ) : D x*C (angle/2) x=C (3*angle/2) x := by
  have h₂ := C_two_mul (angle/2) x
  have h₃ := C_three_mul (angle/2) x
  rw [show 2*(angle/2)=angle by ring] at h₂
  rw [show 3*(angle/2)=3*angle/2 by ring] at h₃
  rw [D,h₂,h₃]
  ring

lemma half_angle_pole_condition {x : ℝ} (hx : -4≤x) :
    4*(angle/2)^2*(-x)<Real.pi^2 := by
  unfold angle
  nlinarith [sq_pos_of_pos Real.pi_pos,mul_nonneg (sq_nonneg Real.pi) (show 0≤x+4 by linarith)]
lemma three_half_angle_pole_condition {x : ℝ} (hx : -4≤x) :
    4*(3*angle/2)^2*(-x)<Real.pi^2 := by
  unfold angle
  nlinarith [sq_pos_of_pos Real.pi_pos,mul_nonneg (sq_nonneg Real.pi) (show 0≤x+4 by linarith)]

lemma cOne_ne_zero {x : ℝ} (hx : -4≤x) : C (angle/2) x≠0 := by
  intro h
  have hp := C_re_pos (by linarith [angle_pos] : 0<angle/2) (half_angle_pole_condition hx)
  rw [h,Complex.zero_re] at hp
  exact lt_irrefl 0 hp
lemma cThree_ne_zero {x : ℝ} (hx : -4≤x) : C (3*angle/2) x≠0 := by
  intro h
  have hp := C_re_pos (by linarith [angle_pos] : 0<3*angle/2) (three_half_angle_pole_condition hx)
  rw [h,Complex.zero_re] at hp
  exact lt_irrefl 0 hp
lemma D_ne_zero_on_source {x : ℝ} (hx : -4≤x) : D x≠0 := by
  intro h
  have he := D_mul_cOne x
  rw [h,zero_mul] at he
  exact cThree_ne_zero hx he.symm

lemma hZero_cosh_ratio {x : ℝ} (hx : -4≤x) :
    hZero x=C (angle/2) x/C (3*angle/2) x := by
  unfold hZero
  apply (eq_div_iff (cThree_ne_zero hx)).mpr
  rw [←D_mul_cOne,←mul_assoc,inv_mul_cancel₀ (D_ne_zero_on_source hx),one_mul]
lemma hOne_cosh_ratio {x : ℝ} (hx : -4≤x) :
    hOne x=C (angle/2) x^2/C (3*angle/2) x := by
  rw [hOne,div_eq_mul_inv,←hZero,hZero_cosh_ratio hx]
  ring

/-- The actual nearest pole is 64/9, with every third pole cancelled. -/
noncomputable def physicalPole (n : ℕ) : ℝ := (64/9)*(2*(n:ℝ)+1)^2
noncomputable def poleFactor (n : ℕ) (x : ℝ) : ℂ := 1+(x:ℂ)/(physicalPole n:ℂ)
noncomputable def hZeroProduct (n : ℕ) (x : ℝ) : ℂ :=
  ∏ j ∈ range n,((poleFactor (3*j) x*poleFactor (3*j+2) x)⁻¹)
noncomputable def hOneProduct (n : ℕ) (x : ℝ) : ℂ :=
  ∏ j ∈ range n,(poleFactor (3*j+1) x/(poleFactor (3*j) x*poleFactor (3*j+2) x))

lemma physicalPole_pos (n : ℕ) : 0<physicalPole n := by unfold physicalPole;positivity
lemma physicalPole_ge (n : ℕ) : 64/9≤physicalPole n := by
  unfold physicalPole
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  nlinarith
lemma poleFactor_re_pos (n : ℕ) {x : ℝ} (hx : -4≤x) : 0<(poleFactor n x).re := by
  have hp:=physicalPole_ge n
  have hpos:=physicalPole_pos n
  rw [poleFactor,←Complex.ofReal_div,←Complex.ofReal_one,←Complex.ofReal_add,Complex.ofReal_re]
  have he : 1+x/physicalPole n=(physicalPole n+x)/physicalPole n := by field_simp
  rw [he]
  exact div_pos (by linarith) hpos
lemma poleFactor_ne_zero (n : ℕ) {x : ℝ} (hx : -4≤x) : poleFactor n x≠0 := by
  intro h
  have hp:=poleFactor_re_pos n hx
  rw [h,Complex.zero_re] at hp
  exact lt_irrefl 0 hp

lemma cEulerProduct_three_half (x : ℝ) (n : ℕ) :
    cEulerProduct (3*angle/2) x n=∏ j ∈ range n,poleFactor j x := by
  unfold cEulerProduct
  apply prod_congr rfl
  intro j hj
  unfold poleFactor physicalPole angle
  push_cast
  have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hjn : 2*(j:ℂ)+1≠0 := by exact_mod_cast (show (2*j+1:ℕ)≠0 by omega)
  field_simp [hp,hjn]
  ring
lemma cEulerProduct_half (x : ℝ) (n : ℕ) :
    cEulerProduct (angle/2) x n=∏ j ∈ range n,poleFactor (3*j+1) x := by
  unfold cEulerProduct
  apply prod_congr rfl
  intro j hj
  unfold poleFactor physicalPole angle
  push_cast
  have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hjn : 2*(j:ℂ)+1≠0 := by exact_mod_cast (show (2*j+1:ℕ)≠0 by omega)
  have hjn' : 2*(3*(j:ℂ)+1)+1≠0 := by exact_mod_cast (show (2*(3*j+1)+1:ℕ)≠0 by omega)
  rw [show (2:ℂ)*(3*(j:ℂ)+1)+1=3*(2*(j:ℂ)+1) by ring]
  field_simp [hp,hjn]
  ring

lemma prod_range_three {R : Type*} [CommMonoid R] (f : ℕ → R) (n : ℕ) :
    (∏ j ∈ range (3*n),f j)=
      (∏ j ∈ range n,f (3*j))*(∏ j ∈ range n,f (3*j+1))*(∏ j ∈ range n,f (3*j+2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3*(n+1)=3*n+2+1 by omega,prod_range_succ,
      show 3*n+2=3*n+1+1 by omega,prod_range_succ,prod_range_succ,ih,
      prod_range_succ,prod_range_succ,prod_range_succ]
    simp only [show 3*n+1+1=3*n+2 by omega]
    ac_rfl

lemma hZeroProduct_eq_ratio (n : ℕ) {x : ℝ} (hx : -4≤x) :
    hZeroProduct n x=cEulerProduct (angle/2) x n/cEulerProduct (3*angle/2) x (3*n) := by
  rw [cEulerProduct_half,cEulerProduct_three_half,prod_range_three]
  unfold hZeroProduct
  rw [prod_inv_distrib,prod_mul_distrib]
  have h₀ : (∏ j ∈ range n,poleFactor (3*j) x)≠0 := prod_ne_zero_iff.mpr (fun j _=>poleFactor_ne_zero _ hx)
  have h₁ : (∏ j ∈ range n,poleFactor (3*j+1) x)≠0 := prod_ne_zero_iff.mpr (fun j _=>poleFactor_ne_zero _ hx)
  have h₂ : (∏ j ∈ range n,poleFactor (3*j+2) x)≠0 := prod_ne_zero_iff.mpr (fun j _=>poleFactor_ne_zero _ hx)
  field_simp

lemma hOneProduct_eq_ratio (n : ℕ) {x : ℝ} (hx : -4≤x) :
    hOneProduct n x=(cEulerProduct (angle/2) x n)^2/cEulerProduct (3*angle/2) x (3*n) := by
  have he : hOneProduct n x=cEulerProduct (angle/2) x n*hZeroProduct n x := by
    rw [cEulerProduct_half,hOneProduct,hZeroProduct,←prod_mul_distrib]
    apply prod_congr rfl
    intro j hj
    exact div_eq_mul_inv _ _
  rw [he,hZeroProduct_eq_ratio n hx]
  ring

lemma tendsto_hZeroProduct {x : ℝ} (hx : -4≤x) :
    Tendsto (fun n=>hZeroProduct n x) atTop (𝓝 (hZero x)) := by
  rw [hZero_cosh_ratio hx]
  have h₀:=tendsto_cEulerProduct (by linarith [angle_pos] : 0<angle/2) (half_angle_pole_condition hx)
  have h₁:=(tendsto_cEulerProduct (by linarith [angle_pos] : 0<3*angle/2)
    (three_half_angle_pole_condition hx)).comp
      (tendsto_id.const_mul_atTop' (by norm_num : (0:ℕ)<3))
  exact (h₀.div h₁ (cThree_ne_zero hx)).congr (fun n=>(hZeroProduct_eq_ratio n hx).symm)

lemma tendsto_hOneProduct {x : ℝ} (hx : -4≤x) :
    Tendsto (fun n=>hOneProduct n x) atTop (𝓝 (hOne x)) := by
  rw [hOne_cosh_ratio hx]
  have h₀:=tendsto_cEulerProduct (by linarith [angle_pos] : 0<angle/2) (half_angle_pole_condition hx)
  have h₁:=(tendsto_cEulerProduct (by linarith [angle_pos] : 0<3*angle/2)
    (three_half_angle_pole_condition hx)).comp
      (tendsto_id.const_mul_atTop' (by norm_num : (0:ℕ)<3))
  exact ((h₀.pow 2).div h₁ (cThree_ne_zero hx)).congr (fun n=>(hOneProduct_eq_ratio n hx).symm)

end CriticalHoneycomb.FiniteFunctional

end

end OAI
