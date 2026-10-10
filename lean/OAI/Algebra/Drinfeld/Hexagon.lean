import OAI.Algebra.Drinfeld.Flatness

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace ComplexKZ

section
open Set Filter FinitePicard KZCollar
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem bulkScale_limit : Tendsto (fun r : ℝ => r/(1+r)) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [Pi.div_apply,add_zero,zero_div] using! h.div ((tendsto_const_nhds (x:=(1:ℝ))).add h) (by norm_num : (1:ℝ)+0≠0)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    change 0<r at hr
    exact div_pos hr (by linarith)

theorem bulk_normalized_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    Tendsto (fun r => gauge (-Y) r*transport (bulkForm X Y) r F.cutoff (bulkEndpoint r)*gauge X r)
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have hh := regularizedBulk_two_limit F hX hY tendsto_id bulkScale_limit
  have ht := (gauge_ratio_limit (-Y)).mul hh
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0<r at hr
  have hd : 1+r≠0 := ne_of_gt (by linarith : 0<1+r)
  have hs : r/(1+r)≠0 := div_ne_zero (ne_of_gt hr) hd
  have he : (1+r)*(r/(1+r))=r := by field_simp
  have hb : 1-r/(1+r)=bulkEndpoint r := by unfold bulkEndpoint; field_simp; ring
  rw [hb,←mul_assoc,←mul_assoc,←gauge_mul_scale (-Y) hd hs,he]
  rfl

end

section
open Set Filter MeasureTheory FinitePicard KZCollar PowerAsymptotic
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A] in
private theorem mass_bound {Ω : ℝ → A} (hc : ContinuousOn Ω (Icc 0 1)) {C : ℝ}
    (h : ∀ t∈Icc 0 1,‖Ω t‖≤C) : integralNorm Ω 0 1≤C := by
  calc
    _ ≤ ∫ t in (0:ℝ)..1,C := intervalIntegral.integral_mono_on (by norm_num)
      (hc.intervalIntegrable_of_Icc (by norm_num)).norm intervalIntegrable_const h
    _ = C := by simp

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem arc_transport_error (X Y : A) (N : ℕ) :
    PowerSmall (fun r => transport (arcForm X Y r) 0 N 1-
      transport (fun _ => angular • X) 0 N 1) := by
  let C := 2*Real.pi*‖Y‖
  let L := Real.pi*‖X‖+C
  apply transport_perturbation_powerSmall (L:=fun _ => L) (E:=fun r => C*r)
    ?_ (const_subpower L) (linear_powerSmall C) N
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)).filter_mono nhdsWithin_le_nhds] with r hr hr1
  have hc := arcForm_continuousOn X Y hr (by linarith : r<1)
  have hb := norm_arcForm_sub_le X Y hr hr1.le
  have hC : 0≤C := by dsimp [C]; positivity
  have he : C*r≤C := mul_le_of_le_one_right hC (by linarith)
  have hX : ‖angular • X‖=Real.pi*‖X‖ := by rw [norm_smul,norm_angular]
  refine ⟨by norm_num,hc.intervalIntegrable_of_Icc (by norm_num),intervalIntegrable_const,
    by dsimp [L]; positivity,mul_nonneg hC hr.le,?_,?_,?_⟩
  · apply mass_bound hc
    intro t ht
    have hh := norm_le_norm_add_norm_sub (angular • X) (arcForm X Y r t)
    rw [hX,norm_sub_rev] at hh
    exact hh.trans (add_le_add le_rfl ((hb t).trans he))
  · apply mass_bound continuousOn_const
    intro t ht
    rw [hX]
    exact le_add_of_nonneg_right hC
  · exact mass_bound (hc.sub continuousOn_const) (fun t _ => hb t)

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem gauge_exp_smul_commute (X : A) (r : ℝ) (c : ℂ) :
    Commute (gauge X r) (NormedSpace.exp (c • X)) := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  exact (((Commute.refl X).smul_left (Real.log r)).smul_right c).exp_left.exp_right

theorem arc_normalized_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) :
    Tendsto (fun r => gauge (-X) r*transport (arcForm X Y r) 0 F.cutoff 1*gauge X r)
      (𝓝[>] 0) (𝓝 (NormedSpace.exp (angular • X))) := by
  have hX' : X∈F.space 1 := by simpa using hX 1
  have hn := pow_cutoff_eq_zero F hX'
  have hneg := pow_cutoff_eq_zero F ((F.space 1).neg_mem hX')
  have herr := normalized_perturbation_limit (arc_transport_error X Y F.cutoff)
    (gauge_subpower hneg) (gauge_subpower hn)
  have hc := constant_transport F (hX angular)
  have he : ∀ r,gauge (-X) r*transport (fun _ => angular • X) 0 F.cutoff 1*gauge X r=
      NormedSpace.exp (angular • X) := by
    intro r
    have hcmt := gauge_exp_smul_commute (-X) r (-angular)
    simp only [neg_smul,smul_neg,neg_neg] at hcmt
    rw [hc,hcmt.eq]
    rw [mul_assoc,gauge_neg_mul,mul_one]
  simp only [he] at herr
  have hh := herr.add_const (NormedSpace.exp (angular • X))
  simpa only [sub_add_cancel,zero_add] using hh

end

open Set Filter FinitePicard KZCollar
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem normalized_cycle (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1)
    {r : ℝ} (hr : 0<r) (hr1 : r<1/2) :
    (gauge (-X) r*transport (arcForm X Y r) 0 F.cutoff 1*gauge X r)*
      (gauge (-X) r*transport (bulkForm (-X-Y) X) r F.cutoff (bulkEndpoint r)*gauge (-X-Y) r)*
      (gauge (-(-X-Y)) r*transport (arcForm (-X-Y) X r) 0 F.cutoff 1*gauge (-X-Y) r)*
      (gauge (-(-X-Y)) r*transport (bulkForm Y (-X-Y)) r F.cutoff (bulkEndpoint r)*gauge Y r)*
      (gauge (-Y) r*transport (arcForm Y (-X-Y) r) 0 F.cutoff 1*gauge Y r)*
      (gauge (-Y) r*transport (bulkForm X Y) r F.cutoff (bulkEndpoint r)*gauge X r)=1 := by
  have hg (u v : A) : gauge u r*(gauge (-u) r*v)=v := by
    rw [←mul_assoc,gauge_mul_neg,one_mul]
  simp only [mul_assoc,hg]
  have h := bulk_arc_identity F hX hY hr hr1
  have hh := congrArg (fun v => gauge (-X) r*v*gauge X r) h
  simpa only [mul_assoc,one_mul,gauge_neg_mul] using hh

theorem associator_hexagon (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1) :
    NormedSpace.exp (angular • X)*associator F (-X-Y) X*
      NormedSpace.exp (angular • (-X-Y))*associator F Y (-X-Y)*
      NormedSpace.exp (angular • Y)*associator F X Y=1 := by
  have hX' : X∈F.space 1 := by simpa using hX 1
  have hY' : Y∈F.space 1 := by simpa using hY 1
  have hZ : ∀ c : ℂ,c • (-X-Y)∈F.space 1 := by
    intro c
    rw [smul_sub,smul_neg]
    exact (F.space 1).sub_mem ((F.space 1).neg_mem (hX c)) (hY c)
  have hZ' : -X-Y∈F.space 1 := by simpa using hZ 1
  have ht := (((((arc_normalized_limit F hX (Y:=Y)).mul
    (bulk_normalized_limit F hZ' hX')).mul (arc_normalized_limit F hZ (Y:=X))).mul
    (bulk_normalized_limit F hY' hZ')).mul (arc_normalized_limit F hY (Y:=-X-Y))).mul
    (bulk_normalized_limit F hX' hY')
  apply tendsto_nhds_unique ht
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)).filter_mono nhdsWithin_le_nhds] with r hr hr1
  exact (normalized_cycle F hX hY hr hr1).symm

end ComplexKZ

namespace PairedHexagon
variable {G : Type*} [Group G]

 theorem meridian (a b c P Q R : G)
    (hp : a*R*c*Q*b*P=1) (hm : a⁻¹*R*c⁻¹*Q*b⁻¹*P=1) :
    R*c^2*R⁻¹=a⁻¹*(P⁻¹*b^2*P)⁻¹*a⁻¹ := by
  have h₁ : R*c*Q=a⁻¹*P⁻¹*b⁻¹ := by
    calc R*c*Q=a⁻¹*(a*R*c*Q*b*P)*P⁻¹*b⁻¹ := by group
         _=a⁻¹*P⁻¹*b⁻¹ := by rw [hp]; group
  have h₂ : R*c⁻¹*Q=a*P⁻¹*b := by
    calc R*c⁻¹*Q=a*(a⁻¹*R*c⁻¹*Q*b⁻¹*P)*P⁻¹*b := by group
         _=a*P⁻¹*b := by rw [hm]; group
  calc R*c^2*R⁻¹=(R*c*Q)*(R*c⁻¹*Q)⁻¹ := by rw [pow_two]; group
       _=(a⁻¹*P⁻¹*b⁻¹)*(a*P⁻¹*b)⁻¹ := by rw [h₁,h₂]
       _=a⁻¹*(P⁻¹*b^2*P)⁻¹*a⁻¹ := by group

 theorem compared_meridian (θ : G →* G) (a b c P Q R V W T : G)
    (hp : a*R*c*Q*b*P=1) (hm : a⁻¹*R*c⁻¹*Q*b⁻¹*P=1)
    (hv : a*T*c*W*b*V=1) (hn : a⁻¹*T*c⁻¹*W*b⁻¹*V=1)
    (ha : θ a=a) (hb : θ (P⁻¹*b^2*P)=V⁻¹*b^2*V) :
    θ (R*c^2*R⁻¹)=T*c^2*T⁻¹ := by
  rw [meridian a b c P Q R hp hm, map_mul,map_mul,map_inv,ha,map_inv,hb,
    meridian a b c V W T hv hn]

 theorem compared_middle (θ : G →* G) (a b c P Q R V W T U H : G)
    (hp : a*R*c*Q*b*P=1) (hv : a*T*c*W*b*V=1)
    (ha : θ a=a) (hb : θ b=U⁻¹*b*U) (hc : θ c=H⁻¹*c*H)
    (hP : U*θ P=V) (hR : θ R=T*H) :
    H*θ Q*U⁻¹=W := by
  have hh := congrArg θ hp
  simp only [map_mul,map_one,ha,hb,hc,hR] at hh
  have he : a*T*c*(H*θ Q*U⁻¹)*b*V=1 := by
    rw [←hP]
    convert hh using 1; group
  have heq : a*T*c*(H*θ Q*U⁻¹)*b*V=a*T*c*W*b*V := he.trans hv.symm
  exact mul_left_cancel (mul_right_cancel (mul_right_cancel heq))
end PairedHexagon

namespace NilpotentExp
open FinitePicard KZCollar
variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A]

 theorem power_difference (F : NilpotentFiltration A) {a b : A}
    (ha : a∈F.space 1) (hb : b∈F.space 1) {n : ℕ} (hd : a-b∈F.space n) (k : ℕ) :
    a^(k+1)-b^(k+1)∈F.space (n+k) := by
  induction k with
  | zero => simpa only [Nat.zero_add,pow_one,Nat.add_zero] using hd
  | succ k ih =>
    have he : a^(k+1+1)-b^(k+1+1)=(a-b)*b^(k+1)+a*(a^(k+1)-b^(k+1)) := by
      simp only [pow_succ',sub_mul,mul_sub]
      abel
    rw [he]
    apply (F.space (n+(k+1))).add_mem
    · exact F.mul_mem n (k+1) hd (pow_mem F hb (k+1))
    · simpa only [show 1+(n+k)=n+(k+1) by omega] using F.mul_mem 1 (n+k) ha ih

 theorem exp_linear (F : NilpotentFiltration A) {a : A} (ha : a∈F.space 1) :
    NormedSpace.exp a=1+a+∑ i∈Finset.range (F.cutoff+1),
      (((i+2).factorial:ℝ)⁻¹) • a^(i+2) := by
  have hz : a^(F.cutoff+2+1)=0 := pow_eq_zero_of_le (by omega) (pow_cutoff_eq_zero F ha)
  have hh := exp_smul_finite a hz 1
  simp only [one_smul,one_pow,one_div] at hh
  rw [Finset.sum_range_succ',Finset.sum_range_succ'] at hh
  simp only [pow_zero,pow_one,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,
    inv_one,one_smul,Nat.zero_add] at hh
  simp only [show ∀ k : ℕ,k+1+1=k+2 from fun k => by omega] at hh
  rw [hh]
  abel

 theorem exp_difference (F : NilpotentFiltration A) {a b : A}
    (ha : a∈F.space 1) (hb : b∈F.space 1) {n : ℕ} (hd : a-b∈F.space n) :
    NormedSpace.exp a-NormedSpace.exp b-(a-b)∈F.space (n+1) := by
  rw [exp_linear F ha,exp_linear F hb]
  have he : 1+a+(∑ i∈Finset.range (F.cutoff+1),(((i+2).factorial:ℝ)⁻¹) • a^(i+2))-
      (1+b+(∑ i∈Finset.range (F.cutoff+1),(((i+2).factorial:ℝ)⁻¹) • b^(i+2)))-(a-b)=
      ∑ i∈Finset.range (F.cutoff+1),(((i+2).factorial:ℝ)⁻¹) • (a^(i+2)-b^(i+2)) := by
    simp only [smul_sub,Finset.sum_sub_distrib]
    abel
  rw [he]
  apply Submodule.sum_mem
  intro i hi
  apply (F.space (n+1)).smul_mem
  exact F.antitone (by omega : n+1≤n+(i+1)) (power_difference F ha hb hd (i+1))

 theorem injective (F : NilpotentFiltration A) {a b : A}
    (ha : a∈F.space 1) (hb : b∈F.space 1) (he : NormedSpace.exp a=NormedSpace.exp b) : a=b := by
  have hh : ∀ n,a-b∈F.space (n+1) := by
    intro n
    induction n with
    | zero => exact (F.space 1).sub_mem ha hb
    | succ n ih =>
      have hc := exp_difference F ha hb ih
      rw [he,sub_self,zero_sub] at hc
      exact (F.space (n+1+1)).neg_mem_iff.mp hc
  have ht := hh F.cutoff
  simpa only [F.terminal,Submodule.mem_bot,sub_eq_zero] using ht

variable [NormedRing B] [NormedAlgebra ℝ B]
 theorem map_exp (f : A →ₐ[ℝ] B) {a : A} {N : ℕ} (ha : a^(N+1)=0) :
    f (NormedSpace.exp a)=NormedSpace.exp (f a) := by
  have hb : (f a)^(N+1)=0 := by rw [←map_pow,ha,map_zero]
  have h₁ := exp_smul_finite a ha 1
  have h₂ := exp_smul_finite (f a) hb 1
  simp only [one_smul] at h₁ h₂
  rw [h₁,h₂,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul,map_pow]
end NilpotentExp

namespace HexagonUnits
open FinitePicard KZCollar
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A]

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A

def exp (a : A) : Aˣ := (NormedSpace.isUnit_exp a).unit
omit [FiniteDimensional ℝ A] in
@[simp] theorem exp_val (a : A) : (exp a:A)=NormedSpace.exp a := (NormedSpace.isUnit_exp a).unit_spec
omit [FiniteDimensional ℝ A] in
@[simp] theorem exp_neg (a : A) : exp (-a)=(exp a)⁻¹ := by
  apply Units.ext
  rw [exp_val]
  rw [←Ring.inverse_exp,←exp_val,Ring.inverse_unit]

def phi (F : NilpotentFiltration A) {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) : Aˣ :=
  (associator_isUnit F hX hY).unit
@[simp] theorem phi_val (F : NilpotentFiltration A) {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    (phi F hX hY:A)=associator F X Y := (associator_isUnit F hX hY).unit_spec

theorem phi_swap (F : NilpotentFiltration A) {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    phi F hY hX=(phi F hX hY)⁻¹ := by
  apply Units.ext
  rw [phi_val,associator_swap F hX hY,←phi_val F hX hY,Ring.inverse_unit]

theorem positive (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1)
    (hX' : X∈F.space 1) (hY' : Y∈F.space 1) (hZ : -X-Y∈F.space 1) :
    exp (ComplexKZ.angular • X)*phi F hZ hX'*exp (ComplexKZ.angular • (-X-Y))*
      phi F hY' hZ*exp (ComplexKZ.angular • Y)*phi F hX' hY'=1 := by
  apply Units.ext
  simpa only [Units.val_mul,exp_val,phi_val,Units.val_one] using
    ComplexKZ.associator_hexagon F hX hY

theorem negative (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1)
    (hX' : X∈F.space 1) (hY' : Y∈F.space 1) (hZ : -X-Y∈F.space 1) :
    (exp (ComplexKZ.angular • X))⁻¹*phi F hZ hX'*(exp (ComplexKZ.angular • (-X-Y)))⁻¹*
      phi F hY' hZ*(exp (ComplexKZ.angular • Y))⁻¹*phi F hX' hY'=1 := by
  have hz : -Y-X= -X-Y := by abel
  have hh := positive F hY hX hY' hX' (hz.symm ▸ hZ)
  simp only [hz,phi_swap F hX' hY',phi_swap F hY' hZ,phi_swap F hZ hX'] at hh
  have hi := congrArg (fun u : Aˣ => (phi F hX' hY')⁻¹*u⁻¹*phi F hX' hY') hh
  convert hi using 1 <;> group

 omit [FiniteDimensional ℝ A] in
 theorem exp_square (a : A) : ((exp a)^2:Aˣ)=exp ((2:ℝ) • a) := by
  apply Units.ext
  simp only [pow_two,Units.val_mul,exp_val,show (2:ℝ) • a=a+a from by simpa using (two_smul ℝ a),
    NormedSpace.exp_add_of_commute (Commute.refl a)]

 theorem exp_map (f : A →ₐ[ℝ] A) (a : A) : Units.map f.toMonoidHom (exp a)=exp (f a) := by
  apply Units.ext
  change f (exp a:A)=(exp (f a):A)
  rw [exp_val,exp_val]
  exact NormedSpace.map_exp f f.toLinearMap.toContinuousLinearMap.continuous a

 omit [FiniteDimensional ℝ A] in
 theorem exp_conj (u : Aˣ) (a : A) : exp ((u:A)*a*((u⁻¹:Aˣ):A))=u*exp a*u⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul,exp_val,NormedSpace.exp_units_conj]
end HexagonUnits

namespace ComplexCutoff
open AssociativeElimination
variable {α : Type*} [Finite α]
variable (P : Set (A ℂ α)) (N : ℕ)

instance normedRing : NormedRing (TruncatedWords.Q P N) :=
  FiniteAlgebraNorm.normedRingOver ℂ _
instance normedAlgebraComplex : NormedAlgebra ℂ (TruncatedWords.Q P N) :=
  FiniteAlgebraNorm.normedAlgebraOver ℂ _
instance normedAlgebraReal : NormedAlgebra ℝ (TruncatedWords.Q P N) :=
  NormedAlgebra.complexToReal
instance finiteReal : FiniteDimensional ℝ (TruncatedWords.Q P N) :=
  Module.Finite.trans ℂ (TruncatedWords.Q P N)

def filtration : FinitePicard.NilpotentFiltration (TruncatedWords.Q P N) where
  space n := (TruncatedWords.filtration P N n).restrictScalars ℝ
  antitone := TruncatedWords.filtration_antitone P N
  one_mem := TruncatedWords.filtration_one P N
  mul_mem := TruncatedWords.filtration_mul P N
  cutoff := N
  terminal := by rw [TruncatedWords.filtration_terminal]; rfl

end ComplexCutoff

namespace ComplexComparison

section
open CutoffDepth HexagonUnits
abbrev F (N : ℕ) := ComplexCutoff.filtration (∅ : Set (AssociativeElimination.A ℂ Bool)) N
abbrev X (N : ℕ) : Q ℂ N := gen N false
abbrev Y (N : ℕ) : Q ℂ N := gen N true
abbrev Z (N : ℕ) : Q ℂ N := -X N-Y N

theorem xm (N : ℕ) : X N∈(F N).space 1 := gen_weight N false
theorem ym (N : ℕ) : Y N∈(F N).space 1 := gen_weight N true
theorem zm (N : ℕ) : Z N∈(F N).space 1 := ((F N).space 1).sub_mem (((F N).space 1).neg_mem (xm N)) (ym N)
theorem xc (N : ℕ) (c : ℂ) : c • X N∈(F N).space 1 :=
  (TruncatedWords.filtration ∅ N 1).smul_mem c (gen_weight (R:=ℂ) N false)
theorem yc (N : ℕ) (c : ℂ) : c • Y N∈(F N).space 1 :=
  (TruncatedWords.filtration ∅ N 1).smul_mem c (gen_weight (R:=ℂ) N true)

def P (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (xm N) (ym N)
def Qq (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (ym N) (zm N)
def Rr (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (zm N) (xm N)
def V (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (((F N).space 1).neg_mem (xm N)) (((F N).space 1).neg_mem (ym N))
def W (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (((F N).space 1).neg_mem (ym N)) (((F N).space 1).neg_mem (zm N))
def T (N : ℕ) : (Q ℂ N)ˣ := phi (F N) (((F N).space 1).neg_mem (zm N)) (((F N).space 1).neg_mem (xm N))
abbrev a (N : ℕ) := exp (ComplexKZ.angular • X N)
abbrev b (N : ℕ) := exp (ComplexKZ.angular • Y N)
abbrev c (N : ℕ) := exp (ComplexKZ.angular • Z N)

theorem p_hex (N : ℕ) : a N*Rr N*c N*Qq N*b N*P N=1 :=
  positive (F N) (xc N) (yc N) (xm N) (ym N) (zm N)
theorem p_hex_neg (N : ℕ) : (a N)⁻¹*Rr N*(c N)⁻¹*Qq N*(b N)⁻¹*P N=1 :=
  negative (F N) (xc N) (yc N) (xm N) (ym N) (zm N)

theorem v_hex (N : ℕ) : a N*T N*c N*W N*b N*V N=1 := by
  have hx : ∀ s : ℂ,s • (-X N)∈(F N).space 1 := fun s => by
    rw [smul_neg]; exact ((F N).space 1).neg_mem (xc N s)
  have hy : ∀ s : ℂ,s • (-Y N)∈(F N).space 1 := fun s => by
    rw [smul_neg]; exact ((F N).space 1).neg_mem (yc N s)
  have hz : -(-X N)-(-Y N)= -Z N := by dsimp [Z]; abel
  have hh := negative (F N) hx hy (((F N).space 1).neg_mem (xm N))
    (((F N).space 1).neg_mem (ym N)) (hz.symm ▸ ((F N).space 1).neg_mem (zm N))
  simpa only [hz,smul_neg,exp_neg,inv_inv,a,b,c,T,W,V] using hh

theorem v_hex_neg (N : ℕ) : (a N)⁻¹*T N*(c N)⁻¹*W N*(b N)⁻¹*V N=1 := by
  have hx : ∀ s : ℂ,s • (-X N)∈(F N).space 1 := fun s => by
    rw [smul_neg]; exact ((F N).space 1).neg_mem (xc N s)
  have hy : ∀ s : ℂ,s • (-Y N)∈(F N).space 1 := fun s => by
    rw [smul_neg]; exact ((F N).space 1).neg_mem (yc N s)
  have hz : -(-X N)-(-Y N)= -Z N := by dsimp [Z]; abel
  have hh := positive (F N) hx hy (((F N).space 1).neg_mem (xm N))
    (((F N).space 1).neg_mem (ym N)) (hz.symm ▸ ((F N).space 1).neg_mem (zm N))
  simpa only [hz,smul_neg,exp_neg,a,b,c,T,W,V] using hh

theorem P_weight (N : ℕ) : (P N:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  change (phi (F N) (xm N) (ym N):Q ℂ N)-1∈(F N).space 1
  rw [phi_val]
  exact KZCollar.associator_sub_one_mem (F N)
    (by apply Submodule.ext; intro u; change u∈TruncatedWords.filtration ∅ N 0 ↔ True
        rw [TruncatedSubstitution.filtration_initial]; simp only [Submodule.mem_top]) (xm N) (ym N)
theorem V_weight (N : ℕ) : (V N:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  change (phi (F N) _ _:Q ℂ N)-1∈(F N).space 1
  rw [phi_val]
  exact KZCollar.associator_sub_one_mem (F N)
    (by apply Submodule.ext; intro u; change u∈TruncatedWords.filtration ∅ N 0 ↔ True
        rw [TruncatedSubstitution.filtration_initial]; simp only [Submodule.mem_top])
    (((F N).space 1).neg_mem (xm N)) (((F N).space 1).neg_mem (ym N))

def theta (N : ℕ) : Q ℂ N ≃ₐ[ℂ] Q ℂ N := ConjugateComparison.theta N (P N) (V N) (P_weight N) (V_weight N)
def U (N : ℕ) : (Q ℂ N)ˣ := ConjugateComparison.unitArrow N (P N) (V N) (P_weight N) (V_weight N)
def H (N : ℕ) : (Q ℂ N)ˣ := (T N)⁻¹*Units.map (theta N).toMonoidHom (Rr N)

theorem theta_x (N : ℕ) : theta N (X N)=X N := ConjugateComparison.theta_x N _ _ _ _
theorem theta_y (N : ℕ) : theta N (Y N)=((U N)⁻¹:(Q ℂ N)ˣ)*Y N*(U N:Q ℂ N) :=
  ConjugateComparison.theta_y N _ _ _ _
theorem U_compare (N : ℕ) : U N*Units.map (theta N).toMonoidHom (P N)=V N := by
  unfold U ConjugateComparison.unitArrow theta
  group

theorem H_compare (N : ℕ) : Units.map (theta N).toMonoidHom (Rr N)=T N*H N := by
  unfold H
  group

def realMap (N : ℕ) : CutoffDepth.Q ℝ N →ₐ[ℝ] Q ℂ N :=
  NilpotentFreeLift.eval (F N) (gen N) (gen_weight N)
@[simp] theorem realMap_gen (N : ℕ) (i : Bool) : realMap N (gen N i)=gen N i :=
  NilpotentFreeLift.eval_gen _ _ _ i

theorem positive_realMap (N : ℕ) : Units.map (realMap N).toMonoidHom (KZComparison.positive N)=P N := by
  apply Units.ext
  change realMap N (KZComparison.positive N:CutoffDepth.Q ℝ N)=(P N:Q ℂ N)
  rw [KZComparison.positive_val]
  change _=(phi (F N) (xm N) (ym N):Q ℂ N)
  simp only [CutoffKZ.X,CutoffKZ.Y]
  rw [phi_val]
  have hh := KZCollar.map_associator (realMap N) (CutoffKZ.weight N) (F N) rfl
    (gen_weight (R:=ℝ) N false) (gen_weight (R:=ℝ) N true)
  change realMap N (KZCollar.associator (CutoffKZ.weight N) (gen N false) (gen N true))=
    KZCollar.associator (F N) (realMap N (gen N false)) (realMap N (gen N true)) at hh
  rw [realMap_gen,realMap_gen] at hh
  exact hh

theorem negative_realMap (N : ℕ) : Units.map (realMap N).toMonoidHom (KZComparison.negative N)=V N := by
  apply Units.ext
  change realMap N (KZComparison.negative N:CutoffDepth.Q ℝ N)=(V N:Q ℂ N)
  rw [KZComparison.negative_val]
  change _=(phi (F N) _ _:Q ℂ N)
  simp only [CutoffKZ.X,CutoffKZ.Y]
  rw [phi_val]
  have hh := KZCollar.map_associator (realMap N) (CutoffKZ.weight N) (F N) rfl
    (((CutoffKZ.weight N).space 1).neg_mem (gen_weight (R:=ℝ) N false))
    (((CutoffKZ.weight N).space 1).neg_mem (gen_weight (R:=ℝ) N true))
  change realMap N (KZCollar.associator (CutoffKZ.weight N) (-gen N false) (-gen N true))=
    KZCollar.associator (F N) (realMap N (-gen N false)) (realMap N (-gen N true)) at hh
  rw [map_neg,map_neg,realMap_gen,realMap_gen] at hh
  exact hh

theorem theta_exp (N : ℕ) (u : Q ℂ N) :
    Units.map (theta N).toMonoidHom (exp u)=exp (theta N u) :=
  exp_map ((theta N).toAlgHom.restrictScalars ℝ) u

theorem exp_smul_conj (N : ℕ) (s : ℂ) (u : (Q ℂ N)ˣ) (v : Q ℂ N) :
    exp (s • ((u:Q ℂ N)*v*((u⁻¹:(Q ℂ N)ˣ):Q ℂ N)))=u*exp (s • v)*u⁻¹ := by
  rw [←smul_mul_assoc,←mul_smul_comm,exp_conj]

theorem theta_a (N : ℕ) : Units.map (theta N).toMonoidHom (a N)=a N := by
  rw [a,theta_exp,map_smul,theta_x]

theorem theta_b (N : ℕ) : Units.map (theta N).toMonoidHom (b N)=(U N)⁻¹*b N*U N := by
  rw [b,theta_exp,map_smul,theta_y]
  simpa only [inv_inv] using exp_smul_conj N ComplexKZ.angular (U N)⁻¹ (Y N)

theorem theta_meridian_y (N : ℕ) :
    Units.map (theta N).toMonoidHom ((P N)⁻¹*(b N)^2*P N)=(V N)⁻¹*(b N)^2*V N := by
  rw [map_mul,map_mul,map_inv,map_pow,theta_b,←U_compare N]
  simp only [pow_two]
  group

theorem theta_meridian_z (N : ℕ) :
    Units.map (theta N).toMonoidHom ((c N)^2)=(H N)⁻¹*(c N)^2*H N := by
  have hh := PairedHexagon.compared_meridian (Units.map (theta N).toMonoidHom)
    (a N) (b N) (c N) (P N) (Qq N) (Rr N) (V N) (W N) (T N)
    (p_hex N) (p_hex_neg N) (v_hex N) (v_hex_neg N) (theta_a N) (theta_meridian_y N)
  simp only [map_mul,map_inv,H_compare] at hh
  have hi := congrArg (fun u : (Q ℂ N)ˣ => (H N)⁻¹*(T N)⁻¹*u*T N*H N) hh
  convert hi using 1 <;> group

theorem conj_weight (N n : ℕ) (u : (Q ℂ N)ˣ) {v : Q ℂ N}
    (hv : v∈TruncatedWords.filtration ∅ N n) :
    (u:Q ℂ N)*v*((u⁻¹:(Q ℂ N)ˣ):Q ℂ N)∈TruncatedWords.filtration ∅ N n := by
  simpa only [Nat.zero_add,Nat.add_zero] using TruncatedWords.filtration_mul ∅ N (0+n) 0
    (TruncatedWords.filtration_mul ∅ N 0 n (ConjugateComparison.mem_zero N (u:Q ℂ N)) hv)
    (ConjugateComparison.mem_zero N ((u⁻¹:(Q ℂ N)ˣ):Q ℂ N))

theorem theta_z (N : ℕ) : theta N (Z N)=((H N)⁻¹:(Q ℂ N)ˣ)*Z N*(H N:Q ℂ N) := by
  let s : ℂ := ComplexKZ.angular+ComplexKZ.angular
  have hs : s≠0 := by
    have ha : ComplexKZ.angular≠0 := by
      intro h
      have hn := ComplexKZ.norm_angular
      rw [h,norm_zero] at hn
      exact Real.pi_ne_zero hn.symm
    dsimp [s]
    intro h
    apply ha
    have h2 : (2:ℂ)*ComplexKZ.angular=0 := by linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hc : (c N)^2=exp (s • Z N) := by
    rw [c,exp_square,two_smul ℝ,←add_smul]
  have hh := theta_meridian_z N
  rw [hc,theta_exp,map_smul] at hh
  have he : exp (s • theta N (Z N))=
      exp (s • (((H N)⁻¹:(Q ℂ N)ˣ)*Z N*(H N:Q ℂ N))) := by
    rw [hh]
    have hh := exp_smul_conj N s (H N)⁻¹ (Z N)
    simpa only [inv_inv] using hh.symm
  have hv := congrArg Units.val he
  simp only [exp_val] at hv
  have h₁ : s • theta N (Z N)∈(F N).space 1 :=
    (TruncatedWords.filtration ∅ N 1).smul_mem s
      (ConjugateComparison.theta_preserves N (P N) (V N) (P_weight N) (V_weight N) 1 (Z N) (zm N))
  have h₂ : s • (((H N)⁻¹:(Q ℂ N)ˣ)*Z N*(H N:Q ℂ N))∈(F N).space 1 :=
    (TruncatedWords.filtration ∅ N 1).smul_mem s
      (by simpa only [inv_inv] using conj_weight N 1 (H N)⁻¹ (zm N))
  exact smul_right_injective (Q ℂ N) hs (NilpotentExp.injective (F N) h₁ h₂ hv)

theorem theta_c (N : ℕ) : Units.map (theta N).toMonoidHom (c N)=(H N)⁻¹*c N*H N := by
  rw [c,theta_exp,map_smul,theta_z]
  simpa only [inv_inv] using exp_smul_conj N ComplexKZ.angular (H N)⁻¹ (Z N)

theorem middle_compare (N : ℕ) : H N*Units.map (theta N).toMonoidHom (Qq N)*(U N)⁻¹=W N :=
  PairedHexagon.compared_middle (Units.map (theta N).toMonoidHom)
    (a N) (b N) (c N) (P N) (Qq N) (Rr N) (V N) (W N) (T N) (U N) (H N)
    (p_hex N) (v_hex N) (theta_a N) (theta_b N) (theta_c N) (U_compare N) (H_compare N)

def rho (N : ℕ) : Q ℂ N →ₐ[ℂ] Q ℂ N :=
  TruncatedSubstitution.subst N (fun i => if i then Z N else Y N)
    (fun i => by cases i; exact ym N; exact zm N)
@[simp] theorem rho_x (N : ℕ) : rho N (X N)=Y N := TruncatedSubstitution.subst_gen N _ _ false
@[simp] theorem rho_y (N : ℕ) : rho N (Y N)=Z N := TruncatedSubstitution.subst_gen N _ _ true
@[simp] theorem rho_z (N : ℕ) : rho N (Z N)=X N := by
  rw [Z,map_sub,map_neg,rho_x,rho_y]
  dsimp [Z]
  abel

theorem rho_three (N : ℕ) (u : Q ℂ N) : rho N (rho N (rho N u))=u := by
  have hh : (rho N).comp ((rho N).comp (rho N))=AlgHom.id ℂ (Q ℂ N) := by
    apply TruncatedSubstitution.hom_ext N
    intro i
    cases i
    · change rho N (rho N (rho N (X N)))=X N
      rw [rho_x,rho_y,rho_z]
    · change rho N (rho N (rho N (Y N)))=Y N
      rw [rho_y,rho_z,rho_x]
  exact AlgHom.congr_fun hh u

theorem rho_phi (N : ℕ) {x y : Q ℂ N}
    (hx : x∈(F N).space 1) (hy : y∈(F N).space 1)
    (hrx : rho N x∈(F N).space 1) (hry : rho N y∈(F N).space 1) :
    Units.map (rho N).toMonoidHom (phi (F N) hx hy)=phi (F N) hrx hry := by
  apply Units.ext
  change rho N (phi (F N) hx hy:Q ℂ N)=(phi (F N) hrx hry:Q ℂ N)
  rw [phi_val,phi_val]
  exact KZCollar.map_associator ((rho N).restrictScalars ℝ) (F N) (F N) rfl hx hy

theorem rho_P (N : ℕ) : Units.map (rho N).toMonoidHom (P N)=Qq N := by
  have hh := rho_phi N (xm N) (ym N) (by rw [rho_x]; exact ym N) (by rw [rho_y]; exact zm N)
  simpa only [rho_x,rho_y,P,Qq,X,Y] using hh

theorem rho_Q (N : ℕ) : Units.map (rho N).toMonoidHom (Qq N)=Rr N := by
  have hh := rho_phi N (ym N) (zm N) (by rw [rho_y]; exact zm N) (by rw [rho_z]; exact xm N)
  simpa only [rho_y,rho_z,Qq,Rr,X,Y] using hh

theorem rho_R (N : ℕ) : Units.map (rho N).toMonoidHom (Rr N)=P N := by
  have hh := rho_phi N (zm N) (xm N) (by rw [rho_z]; exact xm N) (by rw [rho_x]; exact ym N)
  simpa only [rho_z,rho_x,Rr,P,X,Y] using hh

theorem rho_V (N : ℕ) : Units.map (rho N).toMonoidHom (V N)=W N := by
  have hh := rho_phi N (((F N).space 1).neg_mem (xm N)) (((F N).space 1).neg_mem (ym N))
    (by rw [map_neg,rho_x]; exact ((F N).space 1).neg_mem (ym N))
    (by rw [map_neg,rho_y]; exact ((F N).space 1).neg_mem (zm N))
  simpa only [map_neg,rho_x,rho_y,V,W,X,Y] using hh

theorem rho_W (N : ℕ) : Units.map (rho N).toMonoidHom (W N)=T N := by
  have hh := rho_phi N (((F N).space 1).neg_mem (ym N)) (((F N).space 1).neg_mem (zm N))
    (by rw [map_neg,rho_y]; exact ((F N).space 1).neg_mem (zm N))
    (by rw [map_neg,rho_z]; exact ((F N).space 1).neg_mem (xm N))
  simpa only [map_neg,rho_y,rho_z,W,T,X,Y] using hh

theorem rho_T (N : ℕ) : Units.map (rho N).toMonoidHom (T N)=V N := by
  have hh := rho_phi N (((F N).space 1).neg_mem (zm N)) (((F N).space 1).neg_mem (xm N))
    (by rw [map_neg,rho_z]; exact ((F N).space 1).neg_mem (xm N))
    (by rw [map_neg,rho_x]; exact ((F N).space 1).neg_mem (ym N))
  simpa only [map_neg,rho_z,rho_x,T,V,X,Y] using hh

 theorem transport_y (N : ℕ) (p : (Q ℂ N)ˣ) (hp : (p:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1) :
    ConjugateComparison.transport N p hp (Y N)=UnitConjugation.hom (R:=ℂ) p⁻¹ (Y N) := by
  change ConjugateComparison.transport N p hp (TruncatedSubstitution.gen N true)=_
  rw [ConjugateComparison.transport_gen,ConjugateComparison.family,UnitConjugation.hom_apply,inv_inv]
  rfl

theorem rho_theta (N : ℕ) (u : Q ℂ N) :
    rho N (theta N u)=UnitConjugation.hom (R:=ℂ) (U N) (theta N (rho N u)) := by
  let τ := ConjugateComparison.transport N (P N) (P_weight N)
  have he : ((rho N).comp (theta N).toAlgHom).comp τ.toAlgHom=
      ((UnitConjugation.hom (R:=ℂ) (U N)).comp ((theta N).toAlgHom.comp (rho N))).comp τ.toAlgHom := by
    apply TruncatedSubstitution.hom_ext N
    intro i
    cases i
    · change rho N (theta N (τ (X N)))=UnitConjugation.hom (R:=ℂ) (U N) (theta N (rho N (τ (X N))))
      have hτ : τ (X N)=X N := ConjugateComparison.transport_gen N _ _ false
      rw [hτ,theta_x,rho_x,theta_y]
      simp only [UnitConjugation.hom_apply,mul_assoc,Units.mul_inv_cancel_left,Units.mul_inv,mul_one]
    · change rho N (theta N (τ (Y N)))=UnitConjugation.hom (R:=ℂ) (U N) (theta N (rho N (τ (Y N))))
      have h₁ : theta N (τ (Y N))=ConjugateComparison.transport N (V N) (V_weight N) (Y N) :=
        ConjugateComparison.theta_transport N _ _ _ _ _
      rw [h₁,transport_y,UnitConjugation.natural,map_inv,rho_V,rho_y]
      change UnitConjugation.hom (R:=ℂ) (W N)⁻¹ (Z N)=_
      rw [show τ (Y N)=UnitConjugation.hom (R:=ℂ) (P N)⁻¹ (Y N) from transport_y N _ _,
        UnitConjugation.natural,map_inv,rho_P,rho_y]
      rw [show theta N (UnitConjugation.hom (R:=ℂ) (Qq N)⁻¹ (Z N))=
        UnitConjugation.hom (R:=ℂ) (Units.map (theta N).toMonoidHom ((Qq N)⁻¹)) (theta N (Z N)) from
        UnitConjugation.natural (theta N).toAlgHom (Qq N)⁻¹ (Z N),map_inv]
      have hz : theta N (Z N)=UnitConjugation.hom (R:=ℂ) (H N)⁻¹ (Z N) := by
        simpa only [UnitConjugation.hom_apply,inv_inv] using theta_z N
      rw [hz,←UnitConjugation.mul_apply,←UnitConjugation.mul_apply]
      have hm : U N*(Units.map (theta N).toMonoidHom (Qq N))⁻¹*(H N)⁻¹=(W N)⁻¹ := by
        rw [←middle_compare N]
        group
      rw [hm]
  obtain ⟨v,rfl⟩ := τ.surjective u
  exact AlgHom.congr_fun he v

theorem rho_theta_unit (N : ℕ) (u : (Q ℂ N)ˣ) :
    Units.map (rho N).toMonoidHom (Units.map (theta N).toMonoidHom u)=
      U N*Units.map (theta N).toMonoidHom (Units.map (rho N).toMonoidHom u)*(U N)⁻¹ := by
  apply Units.ext
  exact rho_theta N (u:Q ℂ N)

theorem rho_U (N : ℕ) : Units.map (rho N).toMonoidHom (U N)=H N*(U N)⁻¹ := by
  change Units.map (rho N).toMonoidHom (V N*(Units.map (theta N).toMonoidHom (P N))⁻¹)=_
  rw [map_mul,map_inv,rho_V,rho_theta_unit,rho_P,←middle_compare N]
  group

theorem rho_H (N : ℕ) : Units.map (rho N).toMonoidHom (H N)=(U N)⁻¹ := by
  rw [H,map_mul,map_inv,rho_T,rho_theta_unit,rho_R,←U_compare N]
  group

end

section
open CutoffDepth

def cycle : Fin 3 → Fin 3 := ![1,2,0]
def frames (N : ℕ) : Fin 3 → (Q ℂ N)ˣ := ![1,U N,H N]
def rationalWeight (N n : ℕ) : Submodule ℚ (Q ℂ N) :=
  (TruncatedWords.filtration ∅ N n).restrictScalars ℚ

theorem rationalWeight_initial (N : ℕ) : rationalWeight N 0=⊤ := by
  apply Submodule.ext
  intro u
  change u∈TruncatedWords.filtration ∅ N 0 ↔ True
  rw [TruncatedSubstitution.filtration_initial]
  simp only [Submodule.mem_top]
theorem rationalWeight_terminal (N : ℕ) : rationalWeight N (N+2)=⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  have hh := TruncatedWords.filtration_antitone ∅ N (show N+1≤N+2 by omega) hu
  simpa only [TruncatedWords.filtration_terminal,Submodule.mem_bot] using hh

theorem U_weight (N : ℕ) : (U N:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1 :=
  ConjugateComparison.unitArrow_normalized N _ _ _ _

theorem H_weight (N : ℕ) : (H N:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  have he : H N=Units.map (rho N).toMonoidHom (U N)*U N := by rw [rho_U]; group
  rw [he]
  apply ConjugateComparison.mul_normalized N _ _ _ (U_weight N)
  have hh := TruncatedSubstitution.subst_preserves N
    (fun i => if i then Z N else Y N) (fun i => by cases i; exact ym N; exact zm N)
    1 ((U N:Q ℂ N)-1) (U_weight N)
  change rho N ((U N:Q ℂ N)-1)∈_ at hh
  change rho N (U N:Q ℂ N)-1∈_
  simpa only [map_sub,map_one] using hh

theorem frames_weight (N : ℕ) (p : Fin 3) : (frames N p:Q ℂ N)-1∈rationalWeight N 1 := by
  fin_cases p
  · change (1:Q ℂ N)-1∈_
    simp only [sub_self,Submodule.zero_mem]
  · exact U_weight N
  · exact H_weight N

def category (N : ℕ) : LogCategory.Data (Q ℂ N) (Fin 3) :=
  GaugeAutomorphism.data ((theta N).restrictScalars ℚ) (frames N) (rationalWeight N) (N+1)
    (TruncatedWords.filtration_antitone ∅ N) (rationalWeight_initial N) (rationalWeight_terminal N)
    (TruncatedWords.filtration_mul ∅ N)
    (ConjugateComparison.theta_raises N (P N) (V N) (P_weight N) (V_weight N)) (frames_weight N)

def value (N : ℕ) : Q ℂ N := LogCategory.delta (category N) 0 1 1

theorem rho_frames (N : ℕ) (p : Fin 3) :
    Units.map (rho N).toMonoidHom (frames N p)=frames N (cycle p)*(U N)⁻¹ := by
  fin_cases p
  · simp [frames,cycle]
  · exact rho_U N
  · change Units.map (rho N).toMonoidHom (H N)=1*(U N)⁻¹
    simpa only [one_mul] using rho_H N

theorem category_rotate (N : ℕ) (p q : Fin 3) (u : Q ℂ N) :
    rho N ((category N).S p q u)=(category N).S (cycle p) (cycle q) (rho N u) := by
  have hf (p : Fin 3) : rho N (frames N p:Q ℂ N)=(frames N (cycle p)*(U N)⁻¹:(Q ℂ N)ˣ) :=
    congrArg Units.val (rho_frames N p)
  have hi (p : Fin 3) : rho N (((frames N p)⁻¹:(Q ℂ N)ˣ):Q ℂ N)=
      ((frames N (cycle p)*(U N)⁻¹)⁻¹:(Q ℂ N)ˣ) :=
    congrArg (fun v => ((v⁻¹:(Q ℂ N)ˣ):Q ℂ N)) (rho_frames N p)
  simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,
    AlgEquiv.restrictScalars_apply,map_mul,hf,hi,rho_theta,UnitConjugation.hom_apply,
    Units.val_mul,mul_inv_rev,inv_inv,mul_assoc,Units.inv_mul_cancel_left]

theorem delta_rotate (N : ℕ) (p q : Fin 3) (u : Q ℂ N) :
    rho N (LogCategory.delta (category N) p q u)=
      LogCategory.delta (category N) (cycle p) (cycle q) (rho N u) := by
  exact OperatorLog.logarithm_natural (category N).N
    ((category N).S p q-1) ((category N).S (cycle p) (cycle q)-1)
    ((rho N).toLinearMap.restrictScalars ℚ) (by
      intro v
      change rho N ((category N).S p q v-v)=_
      rw [map_sub,category_rotate]
      rfl) u

theorem value_cyclic (N : ℕ) : value N+rho N (value N)+rho N (rho N (value N))=0 := by
  have h₁ : rho N (value N)=LogCategory.delta (category N) 1 2 1 := by
    simpa only [value,cycle,Matrix.cons_val_zero,Matrix.cons_val_one,map_one] using delta_rotate N 0 1 1
  have h₂ : rho N (rho N (value N))=LogCategory.delta (category N) 2 0 1 := by
    rw [h₁,delta_rotate,map_one]
    rfl
  have ha := LogCategory.unit_cocycle (category N) 0 1 2
  have hb := LogCategory.unit_cocycle (category N) 0 2 0
  rw [LogCategory.delta_one_loop] at hb
  change value N+_+_=0
  rw [h₂,h₁]
  change LogCategory.delta (category N) 0 1 1+_+_=0
  rw [add_comm (LogCategory.delta (category N) 0 1 1),←ha,add_comm]
  exact hb.symm
end

open CutoffDepth ConjugateComparison WordGrading

theorem transport_realMap (N : ℕ) (p : (Q ℝ N)ˣ) (q : (Q ℂ N)ˣ)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hq : (q:Q ℂ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : Units.map (realMap N).toMonoidHom p=q) (u : Q ℝ N) :
    realMap N (transport N p hp u)=transport N q hq (realMap N u) := by
  have hv : realMap N (p:Q ℝ N)=(q:Q ℂ N) := congrArg Units.val h
  have hi : realMap N ((p⁻¹:(Q ℝ N)ˣ):Q ℝ N)=((q⁻¹:(Q ℂ N)ˣ):Q ℂ N) :=
    congrArg (fun v => ((v⁻¹:(Q ℂ N)ˣ):Q ℂ N)) h
  have he : (realMap N).comp (transport N p hp).toAlgHom=
      ((transport N q hq).restrictScalars ℝ).toAlgHom.comp (realMap N) := by
    apply TruncatedSubstitution.hom_ext N
    intro b
    change realMap N (transport N p hp (gen N b))=transport N q hq (realMap N (gen N b))
    rw [ConjugateCoalgebra.transport_cutoff_gen,realMap_gen]
    have hqg := transport_gen N q hq b
    change transport N q hq (gen N b)=_ at hqg
    rw [hqg]
    cases b
    · exact realMap_gen N false
    · change realMap N (((p⁻¹:(Q ℝ N)ˣ):Q ℝ N)*gen N true*(p:Q ℝ N))=_
      rw [map_mul,map_mul,hi,hv,realMap_gen]
      rfl
  exact AlgHom.congr_fun he u

theorem theta_realMap (N : ℕ) (u : Q ℝ N) :
    realMap N (KZComparison.theta N u)=theta N (realMap N u) := by
  change realMap N (ConjugateComparison.theta N _ _ _ _ u)=ConjugateComparison.theta N _ _ _ _ (realMap N u)
  rw [ConjugateComparison.theta,AlgEquiv.trans_apply,
    transport_realMap N _ _ (KZComparison.negative_weight N) (V_weight N) (negative_realMap N)]
  have hh := ConjugateCoalgebra.natural_inverse (realMap N)
    (transport N (KZComparison.positive N) (KZComparison.positive_weight N))
    ((transport N (P N) (P_weight N)).restrictScalars ℝ)
    (transport_realMap N _ _ (KZComparison.positive_weight N) (P_weight N) (positive_realMap N)) u
  rw [hh]
  rfl

theorem arrow_realMap (N : ℕ) : Units.map (realMap N).toMonoidHom (KZComparison.arrow N)=U N := by
  have ht : Units.map (realMap N).toMonoidHom
      (Units.map (KZComparison.theta N).toMonoidHom (KZComparison.positive N))=
      Units.map (theta N).toMonoidHom (P N) := by
    apply Units.ext
    change realMap N (KZComparison.theta N (KZComparison.positive N:Q ℝ N))=_
    rw [theta_realMap,show realMap N (KZComparison.positive N:Q ℝ N)=(P N:Q ℂ N) from congrArg Units.val (positive_realMap N)]
    rfl
  change Units.map (realMap N).toMonoidHom (KZComparison.negative N*
    (Units.map (KZComparison.theta N).toMonoidHom (KZComparison.positive N))⁻¹)=_
  rw [map_mul,map_inv,negative_realMap,ht]
  rfl

theorem S_realMap (N : ℕ) (u : Q ℝ N) :
    realMap N ((KZComparison.category N).S false true u)=(category N).S 0 1 (realMap N u) := by
  simp only [KZComparison.category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,
    KZComparison.frames,inv_one,Units.val_one,mul_one]
  change realMap N ((KZComparison.arrow N:Q ℝ N)*KZComparison.theta N u)=_
  rw [map_mul,theta_realMap,show realMap N (KZComparison.arrow N:Q ℝ N)=(U N:Q ℂ N) from congrArg Units.val (arrow_realMap N)]
  simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,frames,
    Matrix.cons_val_zero,Matrix.cons_val_one,inv_one,Units.val_one,mul_one]
  rfl

theorem value_realMap (N : ℕ) : realMap N (KZComparison.value N)=value N := by
  have hh := OperatorLog.logarithm_natural (N+1) ((KZComparison.category N).S false true-1)
    ((category N).S 0 1-1) ((realMap N).toLinearMap.restrictScalars ℚ) (by
      intro u
      change realMap N ((KZComparison.category N).S false true u-u)=_
      rw [map_sub,S_realMap]
      rfl) 1
  change realMap N (KZComparison.value N)=OperatorLog.logarithm (N+1) _ (realMap N 1) at hh
  rw [map_one] at hh
  exact hh

open AssociativeElimination

theorem realMap_word (N : ℕ) (w : FreeMonoid Bool) :
    realMap N (TruncatedWords.quotient ∅ N (word (R:=ℝ) w))=
      TruncatedWords.quotient ∅ N (word (R:=ℂ) w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [word_one,map_one]
  | of_mul a w ih =>
    rw [word_mul,word_mul,word_of,word_of,map_mul,map_mul,map_mul,ih]
    change realMap N (gen N a)*_=gen N a*_
    rw [realMap_gen]

theorem realMap_coefficient (N : ℕ) (w : FreeMonoid Bool) (u : Q ℝ N) :
    TruncatedFree.coefficient N w (realMap N u)=
      ((TruncatedFree.coefficient (R:=ℝ) N w u):ℂ) := by
  classical
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (TruncatedWords.relations (∅:Set (A ℝ Bool)) N) u
  change TruncatedFree.coefficient N w (realMap N (TruncatedWords.quotient ∅ N p))=
    ((TruncatedFree.coefficient (R:=ℝ) N w (TruncatedWords.quotient ∅ N p)):ℂ)
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change TruncatedFree.coefficient N w (realMap N (TruncatedWords.quotient ∅ N (word v)))=
      ((TruncatedFree.coefficient (R:=ℝ) N w (TruncatedWords.quotient ∅ N (word v))):ℂ)
    rw [realMap_word,TruncatedFree.coefficient_quotient,TruncatedFree.coefficient_quotient]
    simp only [word,MonoidAlgebra.coeff_single,Finsupp.single_apply]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add,hp,hq,Complex.ofReal_add]
  | smul c p hp =>
    rw [map_smul,map_smul,LinearMap.map_smul_of_tower,hp]
    rw [map_smul (TruncatedFree.coefficient (R:=ℝ) N w)]
    simp only [Complex.real_smul,smul_eq_mul,Complex.ofReal_mul]

theorem realMap_injective (N : ℕ) : Function.Injective (realMap N) := by
  intro u v huv
  apply (TruncatedFree.equiv (R:=ℝ) (α:=Bool) N).injective
  apply Subtype.ext
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  have hh := congrArg (TruncatedFree.coefficient N w) huv
  rw [realMap_coefficient,realMap_coefficient] at hh
  exact Complex.ofReal_injective hh

def realRotateFamily (N : ℕ) (b : Bool) : Q ℝ N :=
  if b then -gen N false-gen N true else gen N true

theorem realRotateFamily_mem (N : ℕ) (b : Bool) :
    realRotateFamily N b∈(CutoffKZ.weight N).space 1 := by
  cases b
  · exact gen_weight (R:=ℝ) N true
  · exact ((CutoffKZ.weight N).space 1).sub_mem
      (((CutoffKZ.weight N).space 1).neg_mem (gen_weight (R:=ℝ) N false)) (gen_weight (R:=ℝ) N true)

def realRotate (N : ℕ) : Q ℝ N →ₐ[ℝ] Q ℝ N :=
  NilpotentFreeLift.eval (CutoffKZ.weight N) (realRotateFamily N) (realRotateFamily_mem N)

@[simp] theorem realRotate_gen (N : ℕ) (b : Bool) : realRotate N (gen N b)=realRotateFamily N b :=
  NilpotentFreeLift.eval_gen _ _ _ b

theorem rotate_realMap (N : ℕ) (u : Q ℝ N) : realMap N (realRotate N u)=rho N (realMap N u) := by
  have he : (realMap N).comp (realRotate N)=((rho N).restrictScalars ℝ).comp (realMap N) := by
    apply TruncatedSubstitution.hom_ext N
    intro b
    change realMap N (realRotate N (gen N b))=rho N (realMap N (gen N b))
    rw [realMap_gen,realRotate_gen]
    cases b
    · change realMap N (gen N true)=_
      rw [realMap_gen]
      exact (rho_x N).symm
    · change realMap N (-gen N false-gen N true)=_
      rw [map_sub,map_neg,realMap_gen,realMap_gen]
      exact (rho_y N).symm
  exact AlgHom.congr_fun he u

theorem real_value_cyclic (N : ℕ) : KZComparison.value N+realRotate N (KZComparison.value N)+
    realRotate N (realRotate N (KZComparison.value N))=0 := by
  apply realMap_injective N
  rw [map_add,map_add,map_zero,rotate_realMap,rotate_realMap,rotate_realMap,value_realMap]
  exact value_cyclic N
end ComplexComparison

end DeligneDrinfeld

end

end OAI
