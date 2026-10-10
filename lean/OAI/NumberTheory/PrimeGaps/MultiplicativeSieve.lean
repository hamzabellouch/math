import OAI.NumberTheory.PrimeGaps.AdditiveSieve

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

theorem conj_stdAddChar {q : ℕ} [NeZero q] (a : ZMod q) :
    conj (ZMod.stdAddChar a)=ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv]
  exact Circle.coe_inv_eq_conj (ZMod.toCircle a) |>.symm

theorem conj_gaussSum_eq_dft_inverse {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    conj (gaussSum χ ZMod.stdAddChar)=ZMod.dft (χ⁻¹ : DirichletCharacter ℂ q) 1 := by
  simp only [gaussSum,map_sum,map_mul,ZMod.dft_apply,smul_eq_mul,mul_one]
  apply Finset.sum_congr rfl
  intro a _
  rw [conj_stdAddChar]
  have h : conj (χ a)=(χ⁻¹) a := MulChar.star_apply' χ a
  rw [h,mul_comm]

theorem primitive_gauss_mul_conjugate {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar*conj (gaussSum χ ZMod.stdAddChar)=(q:ℂ) := by
  have hf : ZMod.dft χ=(fun k => χ⁻¹ (-k)*gaussSum χ ZMod.stdAddChar) := by
    funext k
    exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hh := congrFun (ZMod.dft_dft χ) (-1)
  rw [hf,ZMod.dft_mul_const,ZMod.dft_comp_neg] at hh
  change ZMod.dft (χ⁻¹ : DirichletCharacter ℂ q) (-(-1))*gaussSum χ ZMod.stdAddChar=_ at hh
  simp only [neg_neg,map_one,smul_eq_mul,mul_one] at hh
  rw [conj_gaussSum_eq_dft_inverse,mul_comm]
  exact hh

theorem primitive_gauss_norm_sq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : ‖gaussSum χ ZMod.stdAddChar‖^2=(q:ℝ) := by
  have h := primitive_gauss_mul_conjugate hχ
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

noncomputable def characterUnitVector {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    EuclideanSpace ℂ (DirichletCharacter ℂ q) := WithLp.toLp 2 (fun χ => χ u)

theorem conj_character_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    conj (χ u)=χ (u.val⁻¹) := by
  change star (χ (u:ZMod q))=_
  rw [MulChar.star_apply',MulChar.inv_apply,Ring.inverse_unit,ZMod.inv_coe_unit]

theorem inner_characterUnitVector {q : ℕ} [NeZero q] (u v : (ZMod q)ˣ) :
    inner ℂ (characterUnitVector u) (characterUnitVector v)=if u=v then (q.totient:ℂ) else 0 := by
  classical
  simp only [PiLp.inner_apply,RCLike.inner_apply,characterUnitVector]
  simp_rw [conj_character_unit]
  have he : (∑ χ : DirichletCharacter ℂ q,χ v*χ (u.val⁻¹))=
      ∑ χ : DirichletCharacter ℂ q,χ (u.val⁻¹)*χ v := by
    apply Finset.sum_congr rfl
    intro χ _
    rw [mul_comm]
  rw [he,DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]
  simp only [Units.val_inj]

theorem character_transform_bound {q : ℕ} [NeZero q] (f : (ZMod q)ˣ→ℂ) :
    (∑ χ : DirichletCharacter ℂ q,‖∑ u : (ZMod q)ˣ, f u*χ u‖^2)≤
      (q.totient:ℝ)*(∑ u : (ZMod q)ˣ,‖f u‖^2) := by
  classical
  have hv : ∀ u : (ZMod q)ˣ,(∑ v : (ZMod q)ˣ,
      ‖inner ℂ (characterUnitVector u) (characterUnitVector v)‖)=(q.totient:ℝ) := by
    intro u
    simp only [inner_characterUnitVector]
    simp_rw [apply_ite norm]
    simp
  have h := norm_sum_smul_sq_le_gram Finset.univ (fun u : (ZMod q)ˣ => characterUnitVector u) f
  simp_rw [hv] at h
  rw [←Finset.sum_mul,mul_comm] at h
  rw [EuclideanSpace.norm_sq_eq] at h
  simpa only [WithLp.ofLp_sum,WithLp.ofLp_smul,characterUnitVector,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul] using h

noncomputable def sequenceCharacterSum {q N : ℕ} (a : Fin N→ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n:Fin N,a n*χ ((n:ℕ):ZMod q)

noncomputable def modularFourierSum {q N : ℕ} [NeZero q] (a : Fin N→ℂ) (u : ZMod q) : ℂ :=
  ∑ n:Fin N,a n*ZMod.stdAddChar (((n:ℕ):ZMod q)*u)

theorem primitive_inverse {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    (χ⁻¹).IsPrimitive := by
  change (χ⁻¹).conductor=q
  rw [DirichletCharacter.conductor_inv]
  exact hχ

theorem multiply_sum_units {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (f : ZMod q→ℂ) :
    (∑ x:ZMod q,χ x*f x)=∑ u:(ZMod q)ˣ,χ u*f u := by
  symm
  apply Fintype.sum_of_injective Units.val Units.val_injective
  · intro x hx
    have hu : ¬IsUnit x := by
      rintro ⟨u,rfl⟩
      exact hx ⟨u,rfl⟩
    rw [MulChar.map_nonunit _ hu,zero_mul]
  · intro u
    rfl

theorem primitive_character_gauss_expansion {q N : ℕ} [NeZero q]
    (a : Fin N→ℂ) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gaussSum (χ⁻¹) ZMod.stdAddChar*sequenceCharacterSum a χ=
      ∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*(χ⁻¹) u := by
  have hg (n:Fin N) := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar
    (primitive_inverse hχ) (((n:ℕ):ZMod q))
  simp only [inv_inv] at hg
  unfold sequenceCharacterSum
  rw [Finset.mul_sum]
  calc
    _ = ∑ n:Fin N,a n*gaussSum (χ⁻¹) (ZMod.stdAddChar.mulShift (((n:ℕ):ZMod q))) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hg]
      ring
    _ = ∑ x:ZMod q,(χ⁻¹) x*modularFourierSum a x := by
      simp only [gaussSum,AddChar.mulShift_apply,Finset.mul_sum,modularFourierSum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = ∑ u:(ZMod q)ˣ,(χ⁻¹) u*modularFourierSum (q:=q) a (u:ZMod q) := multiply_sum_units _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_comm]

theorem primitive_character_energy_le {q N : ℕ} [NeZero q] (a : Fin N→ℂ) :
    (q:ℝ)/(q.totient:ℝ)*
        (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖sequenceCharacterSum a χ‖^2)≤
      ∑ u:(ZMod q)ˣ,‖modularFourierSum (q:=q) a (u:ZMod q)‖^2 := by
  classical
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hs : (q:ℝ)*
        (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖sequenceCharacterSum a χ‖^2)≤
      (q.totient:ℝ)*(∑ u:(ZMod q)ˣ,‖modularFourierSum (q:=q) a (u:ZMod q)‖^2) := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*(χ⁻¹) u‖^2 := by
        apply Finset.sum_congr rfl
        intro χ hχ
        have hp := (Finset.mem_filter.mp hχ).2
        have h := congrArg (fun z:ℂ => ‖z‖^2) (primitive_character_gauss_expansion a hp)
        rwa [norm_mul,mul_pow,primitive_gauss_norm_sq (primitive_inverse hp)] at h
      _ ≤ ∑ χ:DirichletCharacter ℂ q,‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*(χ⁻¹) u‖^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ = ∑ χ:DirichletCharacter ℂ q,‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) a (u:ZMod q)*χ u‖^2 := by
        exact Fintype.sum_bijective (fun χ : DirichletCharacter ℂ q => χ⁻¹)
          inv_involutive.bijective _ _ (fun _ => rfl)
      _ ≤ _ := character_transform_bound _
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hφ).mpr (by simpa only [mul_comm] using hs)

noncomputable def unitFrequency {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) : ℚ := (u.val.val:ℚ)/q

theorem unitFrequency_den {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) : (unitFrequency u).den=q := by
  have hc : Nat.Coprime u.val.val q := (ZMod.isUnit_iff_coprime _ _).mp
    (by simpa only [ZMod.natCast_zmod_val] using u.isUnit)
  have he : unitFrequency u=Rat.divInt (u.val.val:ℤ) (q:ℤ) := by
    rw [Rat.divInt_eq_div]
    simp only [unitFrequency,Int.cast_natCast]
  rw [he,Rat.den_divInt]
  simp only [ite_eq_right (Int.natCast_ne_zero.mpr (NeZero.ne q)), Int.natAbs_natCast,
    Int.gcd_natCast_natCast,hc.symm.gcd_eq_one,Nat.div_one]

theorem unitFrequency_bounds {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    0≤unitFrequency u ∧ unitFrequency u<1 := by
  have hq : (0:ℚ)<q := by exact_mod_cast NeZero.pos q
  exact ⟨div_nonneg (Nat.cast_nonneg _) hq.le,(div_lt_one hq).mpr (by exact_mod_cast ZMod.val_lt u.val)⟩

noncomputable def fareyFrequency {Q : ℕ} (x : Σ q:Fin Q,(ZMod (q.val+1))ˣ) : ℚ := unitFrequency x.2

theorem fareyFrequency_injective (Q : ℕ) :
    Function.Injective (fareyFrequency (Q:=Q)) := by
  rintro ⟨q,u⟩ ⟨r,v⟩ he
  have hd := congrArg Rat.den he
  simp only [fareyFrequency,unitFrequency_den] at hd
  have hqr : q=r := Fin.ext (by omega)
  subst r
  have hv : u=v := by
    apply Units.val_injective
    apply ZMod.val_injective
    change (u.val.val:ℚ)/(q.val+1:ℕ)=(v.val.val:ℚ)/(q.val+1:ℕ) at he
    have hq : ((q.val+1:ℕ):ℚ)≠0 := by positivity
    have he' := (div_left_inj' hq).mp he
    exact_mod_cast he'
  subst v
  rfl

theorem modularFourierSum_eq_bvExp {q N : ℕ} [NeZero q] (a : Fin N→ℂ) (u : (ZMod q)ˣ) :
    modularFourierSum (q:=q) a (u:ZMod q)=
      ∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*(unitFrequency u:ℝ)) := by
  unfold modularFourierSum
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have he : (((n:ℕ)*u.val.val:ℕ):ZMod q)=((n:ℕ):ZMod q)*(u:ZMod q) := by simp
  rw [←he]
  have hh := ZMod.stdAddChar_coe (N:=q) (((n:ℕ)*u.val.val:ℕ):ℤ)
  simp only [Int.cast_natCast] at hh
  rw [hh]
  unfold bvExp unitFrequency
  push_cast
  congr 1
  ring

theorem multiplicative_large_sieve (Q N : ℕ) (a : Fin N→ℂ) :
    (∑ q:Fin Q,((q.val+1:ℕ):ℝ)/((q.val+1).totient:ℝ)*
      (∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ (q.val+1))).filter (fun χ => χ.IsPrimitive),
        ‖sequenceCharacterSum a χ‖^2))≤
      ((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖a n‖^2) := by
  classical
  by_cases hQ : Q=0
  · subst Q
    simp only [Finset.univ_eq_empty,Finset.sum_empty,Nat.cast_zero,zero_pow (by decide : 2≠0),
      zero_mul,add_zero]
    positivity
  have hQpos : 0<Q := Nat.pos_of_ne_zero hQ
  let s : Finset ℚ := Finset.univ.image (fareyFrequency (Q:=Q))
  have hs : ∀ r∈s,0≤r ∧ r<1 ∧ r.den≤Q := by
    intro r hr
    obtain ⟨⟨q,u⟩,_,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨(unitFrequency_bounds u).1,(unitFrequency_bounds u).2,by
      rw [fareyFrequency,unitFrequency_den]
      omega⟩
  calc
    _ ≤ ∑ q:Fin Q,∑ u:(ZMod (q.val+1))ˣ,‖modularFourierSum (q:=q.val+1) a (u:ZMod (q.val+1))‖^2 :=
      Finset.sum_le_sum (fun _ _ => primitive_character_energy_le a)
    _ = ∑ r∈s,‖∑ n:Fin N,a n*bvExp (((n:ℕ):ℝ)*(r:ℝ))‖^2 := by
      dsimp only [s]
      rw [Finset.sum_image (fareyFrequency_injective Q).injOn,Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro u _
      rw [modularFourierSum_eq_bvExp]
      rfl
    _ ≤ _ := rational_additive_large_sieve s hQpos hs N a

theorem weighted_sum_mul_sq_le {ι : Type*} (s : Finset ι) (w f g : ι→ℝ)
    (hw : ∀ i∈s,0≤w i) :
    (∑ i∈s,w i*(f i*g i))^2≤(∑ i∈s,w i*f i^2)*(∑ i∈s,w i*g i^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i _
    exact le_of_eq (by ring)

noncomputable def primitiveCharacterMean (Q : ℕ)
    (f : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) : ℝ :=
  ∑ q:Fin Q,((q.val+1:ℕ):ℝ)/((q.val+1).totient:ℝ)*
    ∑ χ∈(Finset.univ : Finset (DirichletCharacter ℂ (q.val+1))).filter (fun χ=>χ.IsPrimitive),f q χ

theorem primitiveCharacterMean_nonneg {Q : ℕ}
    (f : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ)
    (hf : ∀ q χ,0≤f q χ) : 0≤primitiveCharacterMean Q f := by
  apply Finset.sum_nonneg
  intro q _
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun χ _ => hf q χ))

theorem primitiveCharacterMean_cauchy {Q : ℕ}
    (f g : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
    (primitiveCharacterMean Q (fun q χ=>f q χ*g q χ))^2≤
      primitiveCharacterMean Q (fun q χ=>f q χ^2)*
      primitiveCharacterMean Q (fun q χ=>g q χ^2) := by
  classical
  let w : (Σ q:Fin Q,DirichletCharacter ℂ (q.val+1))→ℝ := fun x =>
    if x.2.IsPrimitive then ((x.1.val+1:ℕ):ℝ)/((x.1.val+1).totient:ℝ) else 0
  have hw (x : Σ q:Fin Q,DirichletCharacter ℂ (q.val+1)) : 0≤w x := by
    dsimp [w]
    split <;> positivity
  have hsum (a : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
      (∑ x : Σ q:Fin Q,DirichletCharacter ℂ (q.val+1),w x*a x.1 x.2)=
        primitiveCharacterMean Q a := by
    rw [Fintype.sum_sigma]
    unfold primitiveCharacterMean
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.mul_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro χ _
    dsimp [w]
    split <;> simp_all
  have h:=weighted_sum_mul_sq_le Finset.univ w (fun x=>f x.1 x.2) (fun x=>g x.1 x.2)
    (fun x _ => hw x)
  rw [←hsum (fun q χ=>f q χ*g q χ),←hsum (fun q χ=>f q χ^2),
    ←hsum (fun q χ=>g q χ^2)]
  exact h

theorem bilinear_multiplicative_large_sieve (Q M N : ℕ) (a : Fin M→ℂ) (b : Fin N→ℂ) :
    (primitiveCharacterMean Q (fun _ χ=>‖sequenceCharacterSum a χ*sequenceCharacterSum b χ‖))^2≤
      (((M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ m:Fin M,‖a m‖^2))*
      (((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖b n‖^2)) := by
  have h:=primitiveCharacterMean_cauchy (Q:=Q)
    (fun _ χ=>‖sequenceCharacterSum a χ‖) (fun _ χ=>‖sequenceCharacterSum b χ‖)
  simp only [norm_mul]
  exact h.trans (mul_le_mul (multiplicative_large_sieve Q M a) (multiplicative_large_sieve Q N b)
    (primitiveCharacterMean_nonneg _ (fun _ _ => sq_nonneg _))
    ((primitiveCharacterMean_nonneg _ (fun _ _ => sq_nonneg _)).trans (multiplicative_large_sieve Q M a)))

theorem sequenceCharacterSum_mul {q M N : ℕ} (a : Fin M→ℂ) (b : Fin N→ℂ)
    (χ : DirichletCharacter ℂ q) :
    sequenceCharacterSum a χ*sequenceCharacterSum b χ=
      ∑ m:Fin M,∑ n:Fin N,a m*b n*χ (((m:ℕ)*(n:ℕ):ℕ):ZMod q) := by
  unfold sequenceCharacterSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Nat.cast_mul,map_mul]
  ring

theorem exponential_kernel_offdiagonal_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (θ : ι→ℝ)
    {D : ℕ} (hD : 0<D)
    (hsep : ∀ i∈s,∀ j∈s,i≠j→∀ m:ℤ,1/(D:ℝ)≤|θ i-θ j-m|)
    (N : ℕ) {i : ι} (hi : i∈s) :
    (∑ j∈s.erase i,‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ j-θ i))‖)≤
      (D:ℝ)*(harmonic D:ℝ) := by
  have h:=exponential_kernel_row_bound s θ hD hsep N hi
  rw [←Finset.sum_erase_add _ _ hi] at h
  have hd : ‖∑ n∈Finset.range N,bvExp ((n:ℝ)*(θ i-θ i))‖=(N:ℝ) := by simp
  rw [hd] at h
  linarith

theorem residue_frequency_separation {q : ℕ} [NeZero q] {a b : ZMod q}
    (hab : a≠b) (m : ℤ) :
    1/(q:ℝ)≤|(a.val:ℝ)/q-(b.val:ℝ)/q-m| := by
  have hz : (a.val:ℤ)-(b.val:ℤ)-m*(q:ℤ)≠0 := by
    intro he
    have h:=congrArg (fun t:ℤ => (t:ZMod q)) he
    simp only [Int.cast_sub,Int.cast_natCast,Int.cast_mul,ZMod.natCast_self,mul_zero,
      sub_zero,Int.cast_zero,ZMod.natCast_zmod_val] at h
    exact hab (sub_eq_zero.mp h)
  have hnum : (1:ℝ)≤|(((a.val:ℤ)-(b.val:ℤ)-m*(q:ℤ)):ℝ)| := by
    exact_mod_cast Int.one_le_abs hz
  have hq : (0:ℝ)<q := by exact_mod_cast NeZero.pos q
  have he : (a.val:ℝ)/q-(b.val:ℝ)/q-m=
      ((((a.val:ℤ)-(b.val:ℤ)-m*(q:ℤ)):ℤ):ℝ)/(q:ℝ) := by
    push_cast
    field_simp
  rw [he,abs_div,abs_of_pos hq]
  simpa only [Int.cast_sub,Int.cast_mul,Int.cast_natCast] using
    div_le_div_of_nonneg_right hnum hq.le

theorem modularFourierSum_one {q N : ℕ} [NeZero q] (u : ZMod q) :
    modularFourierSum (q:=q) (fun _:Fin N=>1) u=
      ∑ n∈Finset.range N,bvExp ((n:ℝ)*((u.val:ℝ)/q)) := by
  unfold modularFourierSum
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  rw [one_mul]
  have he : (((n:ℕ)*u.val:ℕ):ZMod q)=((n:ℕ):ZMod q)*u := by simp
  rw [←he]
  have hh:=ZMod.stdAddChar_coe (N:=q) (((n:ℕ)*u.val:ℕ):ℤ)
  simp only [Int.cast_natCast] at hh
  rw [hh]
  unfold bvExp
  push_cast
  congr 1
  ring

theorem primitive_polya_vinogradov {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (N : ℕ) :
    ‖∑ n:Fin N,χ ((n:ℕ):ZMod q)‖≤Real.sqrt q*(harmonic q:ℝ) := by
  classical
  let : NeZero q := ⟨by omega⟩
  let : Fact (1<q) := ⟨hq⟩
  let θ : ZMod q→ℝ := fun x=>(x.val:ℝ)/q
  let f : ZMod q→ℝ := fun u=>‖∑ n∈Finset.range N,bvExp ((n:ℝ)*θ u)‖
  have hr : (∑ u∈(Finset.univ : Finset (ZMod q)).erase 0,f u)≤(q:ℝ)*(harmonic q:ℝ) := by
    have h:=exponential_kernel_offdiagonal_bound Finset.univ θ (by omega : 0<q)
      (fun _ _ _ _ hne m => residue_frequency_separation hne m) N (Finset.mem_univ (0:ZMod q))
    simpa only [θ,ZMod.val_zero,Nat.cast_zero,zero_div,sub_zero,f] using h
  have hu : Finset.univ.image (fun u:(ZMod q)ˣ=>(u:ZMod q))⊆(Finset.univ : Finset (ZMod q)).erase 0 := by
    intro x hx
    obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨Units.ne_zero u,Finset.mem_univ _⟩
  have hg:=primitive_character_gauss_expansion (fun _:Fin N=>1) hχ
  have hnorm : ‖gaussSum (χ⁻¹) ZMod.stdAddChar‖*
      ‖∑ n:Fin N,χ ((n:ℕ):ZMod q)‖≤(q:ℝ)*(harmonic q:ℝ) := by
    calc
      _ = ‖∑ u:(ZMod q)ˣ,modularFourierSum (q:=q) (fun _:Fin N=>1) (u:ZMod q)*(χ⁻¹) u‖ := by
        simpa only [norm_mul,sequenceCharacterSum,one_mul] using congrArg norm hg
      _ ≤ ∑ u:(ZMod q)ˣ,‖modularFourierSum (q:=q) (fun _:Fin N=>1) (u:ZMod q)*(χ⁻¹) u‖ := norm_sum_le _ _
      _ ≤ ∑ u:(ZMod q)ˣ,f (u:ZMod q) := by
        apply Finset.sum_le_sum
        intro u _
        rw [norm_mul,modularFourierSum_one]
        exact mul_le_of_le_one_right (norm_nonneg _) ((χ⁻¹).norm_le_one _)
      _ = ∑ x∈Finset.univ.image (fun u:(ZMod q)ˣ=>(u:ZMod q)),f x := by
        rw [Finset.sum_image Units.val_injective.injOn]
      _ ≤ ∑ x∈(Finset.univ : Finset (ZMod q)).erase 0,f x :=
        Finset.sum_le_sum_of_subset_of_nonneg hu (fun _ _ _ => norm_nonneg _)
      _ ≤ _ := hr
  have hgn : ‖gaussSum (χ⁻¹) ZMod.stdAddChar‖=Real.sqrt q := by
    have hs:=primitive_gauss_norm_sq (primitive_inverse hχ)
    rw [←hs,Real.sqrt_sq (norm_nonneg _)]
  rw [hgn] at hnorm
  have hsq : (Real.sqrt (q:ℝ))^2=(q:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hpos : 0<Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<q by omega))
  have he : (q:ℝ)*(harmonic q:ℝ)=Real.sqrt q*(Real.sqrt q*(harmonic q:ℝ)) := by
    calc
      _ = (Real.sqrt (q:ℝ))^2*(harmonic q:ℝ) := by rw [hsq]
      _ = _ := by ring
  rw [he] at hnorm
  exact (mul_le_mul_iff_right₀ hpos).mp hnorm

end LargePrimeGaps

end OAI
