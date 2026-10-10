import OAI.NumberTheory.PrimeGaps.MultiplicativeSieve

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

theorem monotone_weighted_prefix_bound (g : ℕ→ℂ) (w : ℕ→ℝ) (hw : Monotone w)
    (hw0 : 0≤w 0) {B : ℝ} (hB : 0≤B) (N : ℕ)
    (hg : ∀ n≤N,‖∑ i∈Finset.range n,g i‖≤B) :
    ‖∑ i∈Finset.range N,(w i:ℂ)*g i‖≤2*w (N-1)*B := by
  have hwpos (n : ℕ) : 0≤w n := hw0.trans (hw (Nat.zero_le n))
  have hd (n : ℕ) : 0≤w (n+1)-w n := sub_nonneg.mpr (hw (by omega))
  have he:=Finset.sum_range_by_parts w g N
  simp only [Complex.real_smul] at he
  rw [he]
  calc
    _ ≤ ‖(w (N-1):ℂ)*(∑ i∈Finset.range N,g i)‖+
        ‖∑ i∈Finset.range (N-1),((w (i+1)-w i:ℝ):ℂ)*(∑ j∈Finset.range (i+1),g j)‖ := norm_sub_le _ _
    _ ≤ w (N-1)*B+(∑ i∈Finset.range (N-1),(w (i+1)-w i)*B) := by
      apply add_le_add
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hwpos _)]
        exact mul_le_mul_of_nonneg_left (hg N le_rfl) (hwpos _)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hd _)]
        exact mul_le_mul_of_nonneg_left (hg (i+1) (by have h:=Finset.mem_range.mp hi; omega)) (hd _)
    _ = w (N-1)*B+(w (N-1)-w 0)*B := by
      rw [←Finset.sum_mul,Finset.sum_range_sub]
    _ ≤ _ := by nlinarith

theorem log_nat_monotone : Monotone (fun n:ℕ=>Real.log n) := by
  intro n m hnm
  by_cases hn : n=0
  · subst n
    simp only [Nat.cast_zero,Real.log_zero]
    by_cases hm : m=0
    · simp [hm]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm)
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn) (by exact_mod_cast hnm)

theorem primitive_log_character_bound {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (N : ℕ) :
    ‖∑ n∈Finset.range N,(Real.log n:ℂ)*χ (n:ZMod q)‖≤
      2*Real.log N*(Real.sqrt q*(harmonic q:ℝ)) := by
  have hH : 0≤(harmonic q:ℝ) := by exact_mod_cast (harmonic_pos (by omega : q≠0)).le
  have hB : 0≤Real.sqrt q*(harmonic q:ℝ) := mul_nonneg (Real.sqrt_nonneg _) hH
  have h:=monotone_weighted_prefix_bound (fun n=>χ (n:ZMod q)) (fun n:ℕ=>Real.log n)
    log_nat_monotone (by simp) hB N (fun n _ => by
      rw [←Fin.sum_univ_eq_sum_range (fun i:ℕ=>χ (i:ZMod q)) n]
      exact primitive_polya_vinogradov hq hχ n)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (log_nat_monotone (Nat.sub_le N 1)) (by norm_num)) hB)

theorem primitive_typeI_log_bound {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (X D : ℕ) (a : ℕ→ℂ) :
    ‖∑ d∈Finset.Icc 1 D,a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),(Real.log n:ℂ)*χ (n:ZMod q))‖≤
      (∑ d∈Finset.Icc 1 D,‖a d‖)*
        (2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ))) := by
  calc
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),(Real.log n:ℂ)*χ (n:ZMod q))‖ := norm_sum_le _ _
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d‖*(2*Real.log (X+1:ℕ)*(Real.sqrt q*(harmonic q:ℝ))) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul,norm_mul]
      apply mul_le_mul
      · exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      · exact (primitive_log_character_bound hq hχ _).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (log_nat_monotone (Nat.add_le_add_right (Nat.div_le_self X d) 1)) (by norm_num))
            (mul_nonneg (Real.sqrt_nonneg _) (by exact_mod_cast (harmonic_pos (by omega : q≠0)).le)))
      · exact norm_nonneg _
      · exact norm_nonneg _
    _ = _ := by rw [Finset.sum_mul]

theorem primitive_typeI_bound {q : ℕ} (hq : 1<q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (X D : ℕ) (a : ℕ→ℂ) :
    ‖∑ d∈Finset.Icc 1 D,a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),χ (n:ZMod q))‖≤
      (∑ d∈Finset.Icc 1 D,‖a d‖)*(Real.sqrt q*(harmonic q:ℝ)) := by
  calc
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d*χ (d:ZMod q)*
      (∑ n∈Finset.range (X/d+1),χ (n:ZMod q))‖ := norm_sum_le _ _
    _ ≤ ∑ d∈Finset.Icc 1 D,‖a d‖*(Real.sqrt q*(harmonic q:ℝ)) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul,norm_mul]
      apply mul_le_mul
      · exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      · rw [←Fin.sum_univ_eq_sum_range (fun i:ℕ=>χ (i:ZMod q)) (X/d+1)]
        exact primitive_polya_vinogradov hq hχ (X/d+1)
      · exact norm_nonneg _
      · exact norm_nonneg _
    _ = _ := by rw [Finset.sum_mul]

noncomputable def sequenceSize {N : ℕ} (a : Fin N→ℂ) : ℝ :=
  Real.sqrt (∑ n:Fin N,‖a n‖^2)

theorem sequenceSize_nonneg {N : ℕ} (a : Fin N→ℂ) : 0 ≤ sequenceSize a := Real.sqrt_nonneg _

theorem sequenceSize_sq {N : ℕ} (a : Fin N→ℂ) :
    sequenceSize a^2=∑ n:Fin N,‖a n‖^2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _=>sq_nonneg _))

noncomputable def sequenceMask {N : ℕ} (p : Fin N→Prop) (a : Fin N→ℂ) : Fin N→ℂ :=
  fun n=>if p n then a n else 0

theorem sequenceMask_size_le {N : ℕ} (p : Fin N→Prop) (a : Fin N→ℂ) :
    sequenceSize (sequenceMask p a) ≤ sequenceSize a := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro n _
  dsimp [sequenceMask]
  split <;> simp

theorem sequenceMask_size_partition {N : ℕ} (p : Fin N→Prop) (a : Fin N→ℂ) :
    sequenceSize (sequenceMask p a)^2+sequenceSize (sequenceMask (fun n=>¬p n) a)^2=
      sequenceSize a^2 := by
  rw [sequenceSize_sq,sequenceSize_sq,sequenceSize_sq,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h:p n <;> simp [sequenceMask,h]

theorem sequenceMask_cauchy {M N : ℕ} (p : Fin M→Prop) (r : Fin N→Prop)
    (a : Fin M→ℂ) (b : Fin N→ℂ) :
    sequenceSize (sequenceMask p a)*sequenceSize (sequenceMask r b)+
      sequenceSize (sequenceMask (fun m=>¬p m) a)*sequenceSize (sequenceMask (fun n=>¬r n) b) ≤
      sequenceSize a*sequenceSize b := by
  have h:=Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Bool)
    (fun z=>if z then sequenceSize (sequenceMask p a) else sequenceSize (sequenceMask (fun m=>¬p m) a))
    (fun z=>if z then sequenceSize (sequenceMask r b) else sequenceSize (sequenceMask (fun n=>¬r n) b))
  simp at h
  rw [sequenceMask_size_partition,sequenceMask_size_partition,←mul_pow] at h
  exact (sq_le_sq₀ (add_nonneg (mul_nonneg (sequenceSize_nonneg _) (sequenceSize_nonneg _))
    (mul_nonneg (sequenceSize_nonneg _) (sequenceSize_nonneg _))) (mul_nonneg (sequenceSize_nonneg a) (sequenceSize_nonneg b))).mp h

noncomputable def sieveBilinearConstant (Q M N : ℕ) : ℝ :=
  Real.sqrt ((M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*
    Real.sqrt ((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))

theorem sieveBilinearConstant_nonneg (Q M N : ℕ) : 0 ≤ sieveBilinearConstant Q M N := by
  unfold sieveBilinearConstant
  positivity

theorem bilinear_primitive_mean_le (Q M N : ℕ) (a : Fin M→ℂ) (b : Fin N→ℂ) :
    primitiveCharacterMean Q (fun _ χ=>‖sequenceCharacterSum a χ*sequenceCharacterSum b χ‖) ≤
      sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b := by
  have h:=bilinear_multiplicative_large_sieve Q M N a b
  have hH : 0 ≤ (harmonic (Q^2):ℝ) := by
    by_cases hh:Q=0
    · simp [hh]
    · exact_mod_cast (harmonic_pos (pow_ne_zero 2 hh)).le
  have hM : 0 ≤ (M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ) := by positivity
  have hN : 0 ≤ (N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ) := by positivity
  have he : (sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b)^2=
      (((M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ m:Fin M,‖a m‖^2))*
      (((N:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ))*(∑ n:Fin N,‖b n‖^2)) := by
    rw [mul_pow,mul_pow,sequenceSize_sq,sequenceSize_sq]
    unfold sieveBilinearConstant
    rw [mul_pow,Real.sq_sqrt hM,Real.sq_sqrt hN]
    ring
  rw [←he] at h
  exact (sq_le_sq₀ (primitiveCharacterMean_nonneg _ (fun _ _=>norm_nonneg _))
    (mul_nonneg (mul_nonneg (sieveBilinearConstant_nonneg _ _ _) (sequenceSize_nonneg _))
      (sequenceSize_nonneg _))).mp h

theorem primitiveCharacterMean_mono {Q : ℕ}
    {f g : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ}
    (h : ∀ q χ,f q χ ≤ g q χ) : primitiveCharacterMean Q f ≤ primitiveCharacterMean Q g := by
  apply Finset.sum_le_sum
  intro q _
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _=>h q χ)) (by positivity)

theorem primitiveCharacterMean_add {Q : ℕ}
    (f g : (q:Fin Q)→DirichletCharacter ℂ (q.val+1)→ℝ) :
    primitiveCharacterMean Q (fun q χ=>f q χ+g q χ)=
      primitiveCharacterMean Q f+primitiveCharacterMean Q g := by
  simp only [primitiveCharacterMean,Finset.sum_add_distrib,mul_add]

noncomputable def triangularCharacterSum {q M N : ℕ} (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m:Fin M,∑ n:Fin N,if n.val<t m then a m*b n*χ (m.val:ZMod q)*χ (n.val:ZMod q) else 0

theorem triangularCharacterSum_split {q M N : ℕ} (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (χ : DirichletCharacter ℂ q) (H : ℕ) :
    triangularCharacterSum a b t χ=
      triangularCharacterSum (sequenceMask (fun m=>t m ≤ H) a) (sequenceMask (fun n=>n.val<H) b) t χ+
      sequenceCharacterSum (sequenceMask (fun m=>¬t m ≤ H) a) χ*
        sequenceCharacterSum (sequenceMask (fun n=>n.val<H) b) χ+
      triangularCharacterSum (sequenceMask (fun m=>¬t m ≤ H) a) (sequenceMask (fun n=>¬n.val<H) b) t χ := by
  unfold triangularCharacterSum sequenceCharacterSum
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hm:t m ≤ H <;> by_cases hn:n.val<H <;> by_cases ht:n.val<t m <;>
    simp [sequenceMask,hm,hn,ht] <;> (try omega) ; ring

theorem triangularCharacterSum_single {q M N L : ℕ} (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (χ : DirichletCharacter ℂ q) (hb : ∀ n,b n≠0→n.val=L) :
    triangularCharacterSum a b t χ=
      sequenceCharacterSum (sequenceMask (fun m=>L<t m) a) χ*sequenceCharacterSum b χ := by
  unfold triangularCharacterSum sequenceCharacterSum
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn:b n=0
  · simp [hn,sequenceMask]
  · have he:=hb n hn
    by_cases ht:L<t m <;> simp [sequenceMask,he,ht] ; ring

theorem triangular_primitive_mean_dyadic (Q M N k L : ℕ) (a : Fin M→ℂ) (b : Fin N→ℂ)
    (t : Fin M→ℕ) (hb : ∀ n,b n≠0→L ≤ n.val ∧ n.val<L+2^k) :
    primitiveCharacterMean Q (fun _ χ=>‖triangularCharacterSum a b t χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b := by
  induction k generalizing L a b with
  | zero =>
    have he (q:Fin Q) (χ : DirichletCharacter ℂ (q.val+1)) :=
      triangularCharacterSum_single a b t χ (fun n hn=>by have h:=hb n hn; simpa using (by omega : n.val=L))
    simp only [he,Nat.cast_zero,zero_add,one_mul]
    exact (bilinear_primitive_mean_le Q M N _ _).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sequenceMask_size_le _ _) (sieveBilinearConstant_nonneg _ _ _))
        (sequenceSize_nonneg _))
  | succ k ih =>
    let H:=L+2^k
    let p : Fin M→Prop := fun m=>t m ≤ H
    let r : Fin N→Prop := fun n=>n.val<H
    let a₀:=sequenceMask p a
    let a₁:=sequenceMask (fun m=>¬p m) a
    let b₀:=sequenceMask r b
    let b₁:=sequenceMask (fun n=>¬r n) b
    have hb₀ : ∀ n,b₀ n≠0→L ≤ n.val ∧ n.val<L+2^k := by
      intro n hn
      have hn' : b n≠0 ∧ n.val<H := by
        dsimp [b₀,sequenceMask,r] at hn
        split at hn <;> simp_all
      exact ⟨(hb n hn'.1).1,hn'.2⟩
    have hb₁ : ∀ n,b₁ n≠0→H ≤ n.val ∧ n.val<H+2^k := by
      intro n hn
      have hn' : b n≠0 ∧ ¬n.val<H := by
        dsimp [b₁,sequenceMask,r] at hn
        split at hn <;> simp_all
      have h:=hb n hn'.1
      simp only [pow_succ] at h
      dsimp [H]
      omega
    have hsplit := primitiveCharacterMean_mono (Q:=Q)
      (f:=fun _ χ=>‖triangularCharacterSum a b t χ‖)
      (g:=fun _ χ=>‖triangularCharacterSum a₀ b₀ t χ‖+
        ‖sequenceCharacterSum a₁ χ*sequenceCharacterSum b₀ χ‖+
        ‖triangularCharacterSum a₁ b₁ t χ‖) (fun _ χ=>by
          rw [triangularCharacterSum_split a b t χ H]
          exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
    rw [primitiveCharacterMean_add,primitiveCharacterMean_add] at hsplit
    have h0:=ih L a₀ b₀ hb₀
    have h1:=ih H a₁ b₁ hb₁
    have hR:=bilinear_primitive_mean_le Q M N a₁ b₀
    have hpair:=sequenceMask_cauchy p r a b
    have hcross : sequenceSize a₁*sequenceSize b₀ ≤ sequenceSize a*sequenceSize b :=
      mul_le_mul (sequenceMask_size_le _ _) (sequenceMask_size_le _ _)
        (sequenceSize_nonneg _) (sequenceSize_nonneg _)
    have hC:=sieveBilinearConstant_nonneg Q M N
    have hk : 0 ≤ (k:ℝ)+1 := by positivity
    have hp:=mul_le_mul_of_nonneg_left hpair (mul_nonneg hk hC)
    have hc:=mul_le_mul_of_nonneg_left hcross hC
    change sequenceSize a₀*sequenceSize b₀+sequenceSize a₁*sequenceSize b₁ ≤ _ at hpair
    change ((k:ℝ)+1)*sieveBilinearConstant Q M N*
      (sequenceSize a₀*sequenceSize b₀+sequenceSize a₁*sequenceSize b₁) ≤ _ at hp
    push_cast
    nlinarith only [hsplit,h0,h1,hR,hp,hc]

theorem triangular_primitive_mean_le (Q M N k : ℕ) (hk : N ≤ 2^k)
    (a : Fin M→ℂ) (b : Fin N→ℂ) (t : Fin M→ℕ) :
    primitiveCharacterMean Q (fun _ χ=>‖triangularCharacterSum a b t χ‖) ≤
      ((k:ℝ)+1)*sieveBilinearConstant Q M N*sequenceSize a*sequenceSize b := by
  apply triangular_primitive_mean_dyadic Q M N k 0 a b t
  intro n _
  exact ⟨Nat.zero_le _,by simpa only [zero_add] using n.isLt.trans_le hk⟩

theorem sum_divisorsAntidiagonal_hyperbola (X : ℕ) (F : ℕ→ℕ→ℂ) :
    (∑ n∈Finset.Icc 1 X,∑ p∈n.divisorsAntidiagonal,F p.1 p.2)=
      ∑ d∈Finset.Icc 1 X,∑ m∈Finset.Icc 1 (X/d),F d m := by
  rw [Finset.sum_sigma',Finset.sum_sigma']
  apply Finset.sum_bij (fun x _ => (⟨x.2.1,x.2.2⟩ : (d:ℕ)×ℕ))
  · rintro ⟨n,d,m⟩ hx
    obtain ⟨hn,hdm⟩:=Finset.mem_sigma.mp hx
    obtain ⟨hn1,hnX⟩:=Finset.mem_Icc.mp hn
    obtain ⟨hdm,hn0⟩:=Nat.mem_divisorsAntidiagonal.mp hdm
    dsimp only at hn1 hnX hdm hn0
    have hd : 0 < d := by
      by_contra hh
      have he : d=0 := by omega
      simp only [he,zero_mul] at hdm
      omega
    have hm : 0 < m := by
      by_contra hh
      have he : m=0 := by omega
      simp only [he,mul_zero] at hdm
      omega
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd,by nlinarith⟩,
      Finset.mem_Icc.mpr ⟨hm,(Nat.le_div_iff_mul_le hd).mpr (by nlinarith)⟩⟩
  · rintro ⟨n,d,m⟩ hx ⟨n',d',m'⟩ hy he
    have hv:(d,m)=(d',m'):=by simpa using congrArg (fun x:(d:ℕ)×ℕ=>(x.1,x.2)) he
    have hd:d=d':=congrArg Prod.fst hv
    have hm:m=m':=congrArg Prod.snd hv
    have hn: d*m = n := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    have hn': d'*m' = n' := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hy).2).1
    subst d'; subst m'
    have hnn:n=n':=hn.symm.trans hn'
    cases hnn; rfl
  · rintro ⟨d,m⟩ hy
    obtain ⟨hd,hm⟩:=Finset.mem_sigma.mp hy
    obtain ⟨hd1,hdX⟩:=Finset.mem_Icc.mp hd
    obtain ⟨hm1,hmX⟩:=Finset.mem_Icc.mp hm
    refine ⟨⟨d*m,(d,m)⟩,?_,rfl⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith,
      by have h: m*d ≤ X:=(Nat.le_div_iff_mul_le hd1).mp hmX; nlinarith⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,by positivity⟩⟩
  · intro x _; rfl

noncomputable def arithmeticCharacterSum {q : ℕ} (X : ℕ) (f : ArithmeticFunction ℝ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n∈Finset.Icc 1 X,(f n:ℂ)*χ (n:ZMod q)

theorem arithmeticCharacterSum_convolution {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f*g) χ=
      ∑ d∈Finset.Icc 1 X,(f d:ℂ)*χ (d:ZMod q)*
        (∑ m∈Finset.Icc 1 (X/d),(g m:ℂ)*χ (m:ZMod q)) := by
  unfold arithmeticCharacterSum
  calc
    _ = ∑ n∈Finset.Icc 1 X,∑ p∈n.divisorsAntidiagonal,
        (f p.1:ℂ)*χ (p.1:ZMod q)*((g p.2:ℂ)*χ (p.2:ZMod q)) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have he: p.1*p.2=n := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [←he,Nat.cast_mul,map_mul]
      ring
    _ = _ := by
      rw [sum_divisorsAntidiagonal_hyperbola X (fun d m=>(f d:ℂ)*χ (d:ZMod q)*((g m:ℂ)*χ (m:ZMod q)))]
      simp only [Finset.mul_sum,mul_assoc]

@[simp] theorem arithmeticCharacterSum_add {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f+g) χ=arithmeticCharacterSum X f χ+arithmeticCharacterSum X g χ := by
  simp [arithmeticCharacterSum,ArithmeticFunction.add_apply,add_mul,Finset.sum_add_distrib]

@[simp] theorem arithmeticCharacterSum_sub {q : ℕ} (X : ℕ)
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X (f-g) χ=arithmeticCharacterSum X f χ-arithmeticCharacterSum X g χ := by
  unfold arithmeticCharacterSum
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  change ((f n-g n:ℝ):ℂ)*χ (n:ZMod q)=_
  push_cast
  ring

theorem vaughan_character_identity {q : ℕ} (X U V : ℕ) (χ : DirichletCharacter ℂ q) :
    arithmeticCharacterSum X ArithmeticFunction.vonMangoldt χ=
      arithmeticCharacterSum X (arithmeticCutoff U ArithmeticFunction.vonMangoldt) χ+
      arithmeticCharacterSum X (arithmeticCutoff V ArithmeticFunction.moebius*ArithmeticFunction.log) χ-
      arithmeticCharacterSum X (arithmeticCutoff V ArithmeticFunction.moebius*
        arithmeticCutoff U ArithmeticFunction.vonMangoldt*ArithmeticFunction.zeta) χ+
      arithmeticCharacterSum X ((ArithmeticFunction.moebius-arithmeticCutoff V ArithmeticFunction.moebius)*
        vaughanSecondCoefficient U) χ := by
  have h:=congrArg (fun f=>arithmeticCharacterSum X f χ) (vaughan_identity U V)
  simpa only [arithmeticCharacterSum_add,arithmeticCharacterSum_sub,vaughanSecondCoefficient,mul_assoc] using h

end LargePrimeGaps

end OAI
