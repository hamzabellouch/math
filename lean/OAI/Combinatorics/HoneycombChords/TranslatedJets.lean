import OAI.Combinatorics.HoneycombChords.PhysicalFactors

namespace OAI

/-! Translated differential equations, Rolle estimates, and confluent positivity.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real

lemma cosineKernelJet_square_cos (t p : ℝ) :
    cosineKernelJet 0 0 (t^2) (-(p^2))=Real.cos (t*p) := by
  rw [cosineKernelJet_zero_zero_cos (sq_nonneg _) (neg_nonpos.mpr (sq_nonneg p)),
    neg_neg,Real.sqrt_sq_eq_abs,Real.sqrt_sq_eq_abs,←abs_mul,Real.cos_abs]

lemma cosineKernelJet_first_negative (t p : ℝ) :
    2*t*cosineKernelJet 1 0 (t^2) (-(p^2))= -p*Real.sin (t*p) := by
  have h := (cosineKernelJet_hasDerivAt_left 0 0 (t^2) (-(p^2))).comp t ((hasDerivAt_id t).pow 2)
  have he : (fun y => cosineKernelJet 0 0 (y^2) (-(p^2)))=(fun y => Real.cos (y*p)) :=
    funext (fun y => cosineKernelJet_square_cos y p)
  have h' : HasDerivAt (fun y => cosineKernelJet 0 0 (y^2) (-(p^2)))
      (2*t*cosineKernelJet 1 0 (t^2) (-(p^2))) t := by
    convert! h using 1 ; simp only [id_eq,pow_one,Nat.cast_ofNat,mul_one,
      Nat.cast_zero,zero_add,show 2-1=1 by omega] ; ring
  rw [he] at h'
  have hc := (Real.hasDerivAt_cos (t*p)).comp t ((hasDerivAt_id t).mul_const p)
  have heq := h'.unique hc
  simp only [one_mul] at heq
  linarith

lemma cosineKernelJet_ode_at_square (t x : ℝ) :
    2*cosineKernelJet 1 0 (t^2) x+8*t^2*cosineKernelJet 2 0 (t^2) x=
      x*cosineKernelJet 0 0 (t^2) x := by
  by_cases hx : 0 ≤ x
  · let p := Real.sqrt x
    have hp : p^2=x := Real.sq_sqrt hx
    have hJ := (cosineKernelJet_hasDerivAt_left 1 0 (t^2) (p^2)).comp t ((hasDerivAt_id t).pow 2)
    have h : HasDerivAt (fun s => 2*s*cosineKernelJet 1 0 (s^2) (p^2))
        (2*cosineKernelJet 1 0 (t^2) (p^2)+8*t^2*cosineKernelJet 2 0 (t^2) (p^2)) t := by
      convert! (((hasDerivAt_id t).const_mul 2).mul hJ) using 1 ;
        simp only [Function.comp_def,Pi.pow_apply,id_eq,pow_one,Nat.cast_ofNat,mul_one,
          show 2-1=1 by omega] ; ring
    have he : (fun s => 2*s*cosineKernelJet 1 0 (s^2) (p^2))=(fun s => p*Real.sinh (s*p)) :=
      funext (fun s => cosineKernelJet_first_square s p)
    rw [he] at h
    have hc := ((Real.hasDerivAt_sinh (t*p)).comp t ((hasDerivAt_id t).mul_const p)).const_mul p
    have hd := h.unique hc
    rw [←cosineKernelJet_square_cosh t p,hp] at hd
    simp only [one_mul] at hd
    calc
      _=p^2*cosineKernelJet 0 0 (t^2) x := by rw [hd];ring
      _=_ := by rw [hp]
  · let p := Real.sqrt (-x)
    have hp : p^2= -x := Real.sq_sqrt (by linarith)
    have hpx : -(p^2)=x := by linarith
    have hJ := (cosineKernelJet_hasDerivAt_left 1 0 (t^2) (-(p^2))).comp t ((hasDerivAt_id t).pow 2)
    have h : HasDerivAt (fun s => 2*s*cosineKernelJet 1 0 (s^2) (-(p^2)))
        (2*cosineKernelJet 1 0 (t^2) (-(p^2))+8*t^2*cosineKernelJet 2 0 (t^2) (-(p^2))) t := by
      convert! (((hasDerivAt_id t).const_mul 2).mul hJ) using 1 ;
        simp only [Function.comp_def,Pi.pow_apply,id_eq,pow_one,Nat.cast_ofNat,mul_one,
          show 2-1=1 by omega] ; ring
    have he : (fun s => 2*s*cosineKernelJet 1 0 (s^2) (-(p^2)))=(fun s => -p*Real.sin (s*p)) :=
      funext (fun s => cosineKernelJet_first_negative s p)
    rw [he] at h
    have hc := ((Real.hasDerivAt_sin (t*p)).comp t ((hasDerivAt_id t).mul_const p)).const_mul (-p)
    have hd := h.unique hc
    rw [←cosineKernelJet_square_cos t p,hpx] at hd
    simp only [one_mul] at hd
    calc
      _= -(p^2)*cosineKernelJet 0 0 (t^2) x := by rw [hd];ring
      _=_ := by rw [hpx]

lemma cosineKernelJet_shifted_ode (j : ℕ) (t x : ℝ) :
    2*cosineKernelJet 1 (j+1) (t^2) x+8*t^2*cosineKernelJet 2 (j+1) (t^2) x=
      x*cosineKernelJet 0 (j+1) (t^2) x+cosineKernelJet 0 j (t^2) x := by
  induction j generalizing x with
  | zero =>
    have hL := ((cosineKernelJet_hasDerivAt_right 1 0 (t^2) x).const_mul 2).add
      ((cosineKernelJet_hasDerivAt_right 2 0 (t^2) x).const_mul (8*t^2))
    have hR := (hasDerivAt_id x).mul (cosineKernelJet_hasDerivAt_right 0 0 (t^2) x)
    have he : (fun y => 2*cosineKernelJet 1 0 (t^2) y+8*t^2*cosineKernelJet 2 0 (t^2) y)=
        (fun y => y*cosineKernelJet 0 0 (t^2) y) := funext (cosineKernelJet_ode_at_square t)
    change HasDerivAt (fun y => 2*cosineKernelJet 1 0 (t^2) y+
      8*t^2*cosineKernelJet 2 0 (t^2) y) _ x at hL
    rw [he] at hL
    have hd := hL.unique hR
    simp only [Nat.cast_zero,zero_add,one_mul,id_eq] at hd
    linarith
  | succ j ih =>
    have hL := ((cosineKernelJet_hasDerivAt_right 1 (j+1) (t^2) x).const_mul 2).add
      ((cosineKernelJet_hasDerivAt_right 2 (j+1) (t^2) x).const_mul (8*t^2))
    have hR := ((hasDerivAt_id x).mul (cosineKernelJet_hasDerivAt_right 0 (j+1) (t^2) x)).add
      (cosineKernelJet_hasDerivAt_right 0 j (t^2) x)
    have he : (fun y => 2*cosineKernelJet 1 (j+1) (t^2) y+8*t^2*cosineKernelJet 2 (j+1) (t^2) y)=
        (fun y => y*cosineKernelJet 0 (j+1) (t^2) y+cosineKernelJet 0 j (t^2) y) := by
      funext y
      exact ih y
    change HasDerivAt (fun y => 2*cosineKernelJet 1 (j+1) (t^2) y+
      8*t^2*cosineKernelJet 2 (j+1) (t^2) y) _ x at hL
    rw [he] at hL
    have hd := hL.unique hR
    simp only [Nat.cast_add,Nat.cast_one,one_mul,id_eq] at hd
    have hn : (j:ℝ)+1+1 ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    linear_combination hd

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section


namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Set

lemma ordered_rolle {n : ℕ} {T : ℝ} {f f' : ℝ → ℝ}
    (x : Fin (n+1) → ℝ) (hx : StrictMono x)
    (hx0 : ∀ i,0 ≤ x i) (hxT : ∀ i,x i ≤ T)
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T,HasDerivAt f (f' t) t)
    (hz : ∀ i,f (x i)=0) :
    ∃ y : Fin n → ℝ,StrictMono y ∧ (∀ i,0 < y i) ∧
      (∀ i,y i < T) ∧ ∀ i,f' (y i)=0 := by
  have h (i : Fin n) : ∃ u ∈ Ioo (x i.castSucc) (x i.succ),f' u=0 := by
    apply exists_hasDerivAt_eq_zero (hx (Fin.castSucc_lt_succ))
      (hc.mono (fun t ht => ⟨(hx0 _).trans ht.1,ht.2.trans (hxT _)⟩))
      (by rw [hz,hz])
    intro t ht
    exact hd t ⟨(hx0 _).trans_lt ht.1,ht.2.trans_le (hxT _)⟩
  choose y hy hz using h
  refine ⟨y,?_,fun i => (hx0 _).trans_lt (hy i).1,
    fun i => (hy i).2.trans_le (hxT _),hz⟩
  intro i j hij
  have hij' : i.succ ≤ j.castSucc := by exact_mod_cast (show i.val+1 ≤ j.val by omega)
  exact (hy i).2.trans_le (hx.monotone hij') |>.trans (hy j).1

lemma ordered_rolle_from_zero {n : ℕ} {T : ℝ} {f f' : ℝ → ℝ}
    (x : Fin n → ℝ) (hx : StrictMono x)
    (hx0 : ∀ i,0 < x i) (hxT : ∀ i,x i < T)
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T,HasDerivAt f (f' t) t)
    (hf0 : f 0=0) (hz : ∀ i,f (x i)=0) :
    ∃ y : Fin n → ℝ,StrictMono y ∧ (∀ i,0 < y i) ∧
      (∀ i,y i < T) ∧ ∀ i,f' (y i)=0 := by
  cases n with
  | zero => exact ⟨x,hx,hx0,hxT,fun i => Fin.elim0 i⟩
  | succ n =>
    have hT : 0 ≤ T := le_trans (hx0 0).le (hxT _).le
    apply ordered_rolle (Fin.cons 0 x)
    · rw [Fin.strictMono_iff_lt_succ]
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx0 0
      · simpa using hx (Fin.castSucc_lt_succ (i:=j))
    · intro i
      exact Fin.cases (by simp) (fun j => by simpa using (hx0 j).le) i
    · intro i
      exact Fin.cases (by simpa using hT) (fun j => by simpa using (hxT j).le) i
    · exact hc
    · exact hd
    · intro i
      exact Fin.cases (by simpa using hf0) (fun j => by simpa using hz j) i

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Set Finset

/-- The exact two-step positive differential system supplied by translating the
cosine kernel below its first zero. It does not assume any determinant sign. -/
structure SturmPowerFamily (T : ℝ) where
  F : ℕ → ℝ → ℝ
  H : ℕ → ℝ → ℝ
  w : ℝ → ℝ
  wpos : ∀ t ∈ Ioo 0 T,0 < w t
  Fcontinuous : ∀ j,ContinuousOn (F j) (Icc 0 T)
  Hcontinuous : ∀ j,ContinuousOn (H j) (Icc 0 T)
  Fderiv : ∀ j t,t ∈ Ioo 0 T → HasDerivAt (F j) (H j t/w t) t
  Hderiv : ∀ j t,t ∈ Ioo 0 T → HasDerivAt (H (j+1)) (w t*F j t) t
  Fzero : ∀ t ∈ Icc 0 T,F 0 t=1
  Hzero : ∀ t ∈ Icc 0 T,H 0 t=0
  Finit : ∀ j,0 < j → F j 0=0
  Hinit : ∀ j,H j 0=0

namespace SturmPowerFamily
variable {T : ℝ} (S : SturmPowerFamily T)

noncomputable def combination {n : ℕ} (G : ℕ → ℝ → ℝ) (e : Fin n → ℕ)
    (c : Fin n → ℝ) (t : ℝ) : ℝ := ∑ i,c i*G (e i) t

lemma combination_continuous {n : ℕ} (G : ℕ → ℝ → ℝ)
    (hG : ∀ j,ContinuousOn (G j) (Icc 0 T)) (e : Fin n → ℕ) (c : Fin n → ℝ) :
    ContinuousOn (combination G e c) (Icc 0 T) := by
  exact continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (hG (e i)))

lemma combination_Fderiv {n : ℕ} (e : Fin n → ℕ) (c : Fin n → ℝ)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (combination S.F e c) (combination S.H e c t/S.w t) t := by
  have h := HasDerivAt.sum (fun i (_ : i ∈ (univ : Finset (Fin n))) => (S.Fderiv (e i) t ht).const_mul (c i))
  convert! h using 1
  · funext y;simp [combination]
  · simp only [combination,sum_div]
    apply sum_congr rfl
    intro i hi
    ring

lemma combination_Hderiv {n : ℕ} (e : Fin n → ℕ) (c : Fin n → ℝ)
    (he : ∀ i,0 < e i) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (combination S.H e c)
      (S.w t*combination S.F (fun i => e i-1) c t) t := by
  have h := HasDerivAt.sum (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
    (show HasDerivAt (S.H (e i)) (S.w t*S.F (e i-1) t) t from
      by simpa only [Nat.sub_add_cancel (he i)] using S.Hderiv (e i-1) t ht).const_mul (c i))
  convert! h using 1
  · funext y;simp [combination]
  · simp only [combination,mul_sum]
    apply sum_congr rfl
    intro i hi
    ring

lemma lower_H_roots {n : ℕ} (e : Fin n → ℕ) (c : Fin n → ℝ)
    (he : ∀ i,0 < e i) (x : Fin n → ℝ) (hx : StrictMono x)
    (hx0 : ∀ i,0 < x i) (hxT : ∀ i,x i < T)
    (hz : ∀ i,combination S.H e c (x i)=0) :
    ∃ y : Fin n → ℝ,StrictMono y ∧ (∀ i,0 < y i) ∧
      (∀ i,y i < T) ∧ ∀ i,combination S.F (fun i => e i-1) c (y i)=0 := by
  obtain ⟨y,hy,hy0,hyT,hyz⟩ := ordered_rolle_from_zero x hx hx0 hxT
    (combination_continuous S.H S.Hcontinuous e c)
    (fun t ht => S.combination_Hderiv e c he ht)
    (by simp [combination,S.Hinit]) hz
  refine ⟨y,hy,hy0,hyT,fun i => ?_⟩
  exact (mul_eq_zero.mp (hyz i)).resolve_left (ne_of_gt (S.wpos _ ⟨hy0 i,hyT i⟩))

lemma sparse_unique_bounded (d : ℕ) :
    ∀ {n : ℕ} (e : Fin n → ℕ),StrictMono e → (∀ i,e i < d) →
      ∀ (c : Fin n → ℝ) (x : Fin n → ℝ),StrictMono x →
      (∀ i,0 < x i) → (∀ i,x i < T) →
      (∀ i,combination S.F e c (x i)=0) → c=0 := by
  induction d with
  | zero =>
    intro n e he hd c x hx hx0 hxT hz
    funext i
    exact False.elim (Nat.not_lt_zero _ (hd i))
  | succ d ih =>
    intro n e he hd c x hx hx0 hxT hz
    cases n with
    | zero => exact Subsingleton.elim _ _
    | succ n =>
      by_cases he0 : e 0=0
      · obtain ⟨y,hy,hy0,hyT,hyz⟩ := ordered_rolle x hx
          (fun i => (hx0 i).le) (fun i => (hxT i).le)
          (combination_continuous S.F S.Fcontinuous e c)
          (fun t ht => S.combination_Fderiv e c ht) hz
        let e' : Fin n → ℕ := fun i => e i.succ
        let c' : Fin n → ℝ := fun i => c i.succ
        have he' : ∀ i,0 < e' i := by
          intro i
          have h := he (show (0 : Fin (n+1)) < i.succ by change 0 < i.val+1;omega)
          simpa [he0,e'] using h
        have hyz' : ∀ i,combination S.H e' c' (y i)=0 := by
          intro i
          have h := (div_eq_zero_iff.mp (hyz i)).resolve_right
            (ne_of_gt (S.wpos _ ⟨hy0 i,hyT i⟩))
          simpa [combination,Fin.sum_univ_succ,he0,S.Hzero _ ⟨(hy0 i).le,(hyT i).le⟩,e',c'] using h
        obtain ⟨z,hzmono,hz0,hzT,hzz⟩ := S.lower_H_roots e' c' he' y hy hy0 hyT hyz'
        have hcm : c'=0 := ih (fun i => e' i-1)
          (by intro i j hij;have h := he (Fin.succ_lt_succ_iff.mpr hij);have h0:=he' i;dsimp [e'] at *;omega)
          (by intro i;have h:=hd i.succ;have h0:=he' i;dsimp [e'] at *;omega)
          c' z hzmono hz0 hzT hzz
        have hcS (i : Fin n) : c i.succ=0 := congrFun hcm i
        have hc0 : c 0=0 := by
          have h:=hz 0
          simpa [combination,Fin.sum_univ_succ,he0,S.Fzero _ ⟨(hx0 0).le,(hxT 0).le⟩,hcS] using h
        funext i
        exact Fin.cases hc0 hcS i
      · have hep : ∀ i,0 < e i := by
          intro i
          have h := he.monotone (Fin.zero_le i)
          omega
        have hinit : combination S.F e c 0=0 := by
          simp [combination,fun i => S.Finit (e i) (hep i)]
        obtain ⟨y,hy,hy0,hyT,hyz⟩ := ordered_rolle_from_zero x hx hx0 hxT
          (combination_continuous S.F S.Fcontinuous e c)
          (fun t ht => S.combination_Fderiv e c ht) hinit hz
        have hyz' : ∀ i,combination S.H e c (y i)=0 := fun i =>
          (div_eq_zero_iff.mp (hyz i)).resolve_right (ne_of_gt (S.wpos _ ⟨hy0 i,hyT i⟩))
        obtain ⟨z,hzmono,hz0,hzT,hzz⟩ := S.lower_H_roots e c hep y hy hy0 hyT hyz'
        exact ih (fun i => e i-1)
          (by intro i j hij;have h:=he hij;have h0:=hep i;change e i-1 < e j-1;omega)
          (by intro i;have h:=hd i;have h0:=hep i;omega)
          c z hzmono hz0 hzT hzz

lemma sparse_unique {n : ℕ} (e : Fin n → ℕ) (he : StrictMono e)
    (c : Fin n → ℝ) (x : Fin n → ℝ) (hx : StrictMono x)
    (hx0 : ∀ i,0 < x i) (hxT : ∀ i,x i < T)
    (hz : ∀ i,combination S.F e c (x i)=0) : c=0 := by
  classical
  exact S.sparse_unique_bounded (univ.sup e+1) e he
    (fun i => Nat.lt_succ_of_le (le_sup (f:=e) (mem_univ i))) c x hx hx0 hxT hz

end SturmPowerFamily
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Set

noncomputable def translatedU (a : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  cosineKernelJet 0 j (t^2) (-a)
noncomputable def translatedUPrime (a : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  2*t*cosineKernelJet 1 j (t^2) (-a)
noncomputable def translatedF (a : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  translatedU a j t/translatedU a 0 t
noncomputable def translatedH (a : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  translatedUPrime a j t*translatedU a 0 t-translatedU a j t*translatedUPrime a 0 t

lemma translatedU_hasDerivAt (a : ℝ) (j : ℕ) (t : ℝ) :
    HasDerivAt (translatedU a j) (translatedUPrime a j t) t := by
  have h := (cosineKernelJet_hasDerivAt_left 0 j (t^2) (-a)).comp t ((hasDerivAt_id t).pow 2)
  convert! h using 1 ; simp only [translatedUPrime,id_eq,
    pow_one,Nat.cast_ofNat,mul_one,Nat.cast_zero,zero_add,show 2-1=1 by omega] ; ring

lemma translatedUPrime_hasDerivAt (a : ℝ) (j : ℕ) (t : ℝ) :
    HasDerivAt (translatedUPrime a j)
      (2*cosineKernelJet 1 j (t^2) (-a)+8*t^2*cosineKernelJet 2 j (t^2) (-a)) t := by
  have hJ := (cosineKernelJet_hasDerivAt_left 1 j (t^2) (-a)).comp t ((hasDerivAt_id t).pow 2)
  convert! (((hasDerivAt_id t).const_mul 2).mul hJ) using 1 ;
    simp only [Function.comp_def,Pi.pow_apply,id_eq,pow_one,
      Nat.cast_ofNat,mul_one,show 2-1=1 by omega] ; ring

lemma translatedUPrime_zero_deriv (a t : ℝ) :
    HasDerivAt (translatedUPrime a 0) (-a*translatedU a 0 t) t := by
  simpa only [cosineKernelJet_ode_at_square,translatedU] using translatedUPrime_hasDerivAt a 0 t
lemma translatedUPrime_succ_deriv (a t : ℝ) (j : ℕ) :
    HasDerivAt (translatedUPrime a (j+1)) (-a*translatedU a (j+1) t+translatedU a j t) t := by
  simpa only [cosineKernelJet_shifted_ode,translatedU] using translatedUPrime_hasDerivAt a (j+1) t

lemma translatedU_zero_eq_cos {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    translatedU a 0 t=Real.cos (t*Real.sqrt a) := by
  simpa only [Real.sq_sqrt ha,translatedU] using cosineKernelJet_square_cos t (Real.sqrt a)

lemma translatedU_zero_pos {a T : ℝ} (ha : 0 ≤ a) (hT : T*Real.sqrt a < Real.pi/2)
    {t : ℝ} (ht : t ∈ Icc 0 T) : 0 < translatedU a 0 t := by
  rw [translatedU_zero_eq_cos ha]
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hp : 0 < Real.pi/2 := by positivity
    have hx : 0 ≤ t*Real.sqrt a := mul_nonneg ht.1 (Real.sqrt_nonneg a)
    linarith
  · exact (mul_le_mul_of_nonneg_right ht.2 (Real.sqrt_nonneg a)).trans_lt hT

lemma translatedF_hasDerivAt {a t : ℝ} (j : ℕ) (hc : translatedU a 0 t ≠ 0) :
    HasDerivAt (translatedF a j) (translatedH a j t/(translatedU a 0 t)^2) t := by
  exact (translatedU_hasDerivAt a j t).div (translatedU_hasDerivAt a 0 t) hc

lemma translatedH_succ_deriv (a t : ℝ) (j : ℕ) :
    HasDerivAt (translatedH a (j+1)) (translatedU a 0 t*translatedU a j t) t := by
  have h := ((translatedUPrime_succ_deriv a t j).mul (translatedU_hasDerivAt a 0 t)).sub
    ((translatedU_hasDerivAt a (j+1) t).mul (translatedUPrime_zero_deriv a t))
  convert! h using 1 ; first | rfl | ring

lemma translatedU_initial (a : ℝ) (j : ℕ) :
    translatedU a j 0=if j=0 then 1 else 0 := by
  simp only [translatedU,zero_pow (by omega : 2 ≠ 0),cosineKernelJet,kernelJetTerm,
    polynomialJet_at_zero_X_pow]
  rw [tsum_eq_single 0]
  · simp [polynomialJet,Polynomial.coeff_one]
  · intro k hk
    simp [hk]

lemma translatedH_initial (a : ℝ) (j : ℕ) : translatedH a j 0=0 := by
  simp [translatedH,translatedUPrime]

noncomputable def translatedSturmFamily {a T : ℝ} (ha : 0 ≤ a)
    (hT : T*Real.sqrt a < Real.pi/2) : SturmPowerFamily T where
  F := translatedF a
  H := translatedH a
  w := fun t => (translatedU a 0 t)^2
  wpos := fun t ht => sq_pos_of_pos (translatedU_zero_pos ha hT ⟨ht.1.le,ht.2.le⟩)
  Fcontinuous := fun j => by
    intro t ht
    exact (translatedF_hasDerivAt j (ne_of_gt (translatedU_zero_pos ha hT ht))).continuousAt.continuousWithinAt
  Hcontinuous := fun j => by
    intro t ht
    exact (((translatedUPrime_hasDerivAt a j t).continuousAt.mul (translatedU_hasDerivAt a 0 t).continuousAt).sub
      ((translatedU_hasDerivAt a j t).continuousAt.mul (translatedUPrime_hasDerivAt a 0 t).continuousAt)).continuousWithinAt
  Fderiv := fun j t ht => translatedF_hasDerivAt j (ne_of_gt (translatedU_zero_pos ha hT ⟨ht.1.le,ht.2.le⟩))
  Hderiv := fun j t ht => by
    have hc := ne_of_gt (translatedU_zero_pos ha hT ⟨ht.1.le,ht.2.le⟩)
    convert translatedH_succ_deriv a t j using 1
    simp only [translatedF]
    field_simp

  Fzero := fun t ht => div_self (ne_of_gt (translatedU_zero_pos ha hT ht))
  Hzero := fun t ht => by unfold translatedH;ring
  Finit := fun j hj => by simp [translatedF,translatedU_initial,Nat.ne_of_gt hj]
  Hinit := translatedH_initial a

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Set Finset

lemma translatedU_parameter_continuous (j : ℕ) (t : ℝ) :
    Continuous (fun a => translatedU a j t) := by
  exact (cosineKernelJet_contDiff_right 0 j (t^2) 0).continuous.comp continuous_neg

lemma translatedU_parameter_zero (j : ℕ) (t : ℝ) :
    translatedU 0 j t=(t^2)^j/(2*j).factorial := by
  simp only [translatedU,neg_zero,cosineKernelJet_symm 0 j]
  exact cosineKernelJet_at_zero j (t^2)

lemma translatedU_det_ne_zero {n : ℕ} {a T : ℝ} (ha : 0 ≤ a)
    (hT : T*Real.sqrt a < Real.pi/2) (e : Fin n → ℕ) (he : StrictMono e)
    (t : Fin n → ℝ) (ht : StrictMono t) (ht0 : ∀ i,0 < t i) (htT : ∀ i,t i < T) :
    Matrix.det (fun i j => translatedU a (e i) (t j)) ≠ 0 := by
  classical
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hz : ∀ j,SturmPowerFamily.combination (translatedSturmFamily ha hT).F e c (t j)=0 := by
    intro j
    have h := congrFun hc j
    simp only [Matrix.row,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at h
    change ∑ k,c k*(translatedU a (e k) (t j)/translatedU a 0 (t j))=0
    simp_rw [←mul_div_assoc,←sum_div]
    rw [h,zero_div]
  have hz' := (translatedSturmFamily ha hT).sparse_unique e he c t ht ht0 htT hz
  exact congrFun hz' i

lemma translatedU_det_pos_zero {n : ℕ} (e : Fin n → ℕ) (he : StrictMono e)
    (t : Fin n → ℝ) (ht : StrictMono t) (ht0 : ∀ i,0 < t i) :
    0 < Matrix.det (fun i j => translatedU 0 (e i) (t j)) := by
  simp_rw [translatedU_parameter_zero,div_eq_inv_mul]
  change 0 < (Matrix.of (fun i j => ((2*e i).factorial:ℝ)⁻¹*(t j^2)^e i)).det
  have hd := Matrix.det_mul_column (fun i => ((2*e i).factorial:ℝ)⁻¹) (Matrix.of (fun i j => (t j^2)^e i))
  simp only [Matrix.of_apply] at hd
  rw [hd]
  apply mul_pos (prod_pos (fun i _ => by positivity))
  apply power_det_pos e (fun i => (t i)^2) he
  · intro i j hij
    exact pow_lt_pow_left₀ (ht hij) (ht0 i).le (by omega : 2 ≠ 0)
  · intro i
    exact sq_pos_of_pos (ht0 i)

lemma translatedU_det_pos {n : ℕ} {a T : ℝ} (ha : 0 ≤ a) (hT0 : 0 ≤ T)
    (hT : T*Real.sqrt a < Real.pi/2) (e : Fin n → ℕ) (he : StrictMono e)
    (t : Fin n → ℝ) (ht : StrictMono t) (ht0 : ∀ i,0 < t i) (htT : ∀ i,t i < T) :
    0 < Matrix.det (fun i j => translatedU a (e i) (t j)) := by
  let f : ℝ → ℝ := fun b => Matrix.det (fun i j => translatedU b (e i) (t j))
  have hf : Continuous f := by
    apply Continuous.matrix_det
    exact continuous_pi (fun i => continuous_pi (fun j => translatedU_parameter_continuous (e i) (t j)))
  have h0 : 0 < f 0 := translatedU_det_pos_zero e he t ht ht0
  have hne : ∀ b ∈ Icc 0 a,f b ≠ 0 := by
    intro b hb
    apply translatedU_det_ne_zero hb.1 _ e he t ht ht0 htT
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb.2) hT0).trans_lt hT
  by_contra hneg
  have hh : f a ≤ 0 := le_of_not_gt hneg
  obtain ⟨b,hb,hbz⟩ := intermediate_value_Icc' ha hf.continuousOn ⟨hh,h0.le⟩
  exact hne b hb hbz

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Set Filter Topology

lemma translated_beta_eval_det_pos {n : ℕ} {a R : ℝ} (ha : 0 ≤ a)
    (hphase : Real.sqrt R*Real.sqrt a < Real.pi/2)
    (b : Fin n → ℝ) (hb : StrictMono b) (hb0 : ∀ i,0 < b i) (hbR : ∀ i,b i < R)
    (e : Fin n → ℕ) (he : StrictMono e) :
    0 < Matrix.det (fun i j => cosineKernelJet 0 (e i) (b j) (-a)) := by
  have hp := translatedU_det_pos ha (Real.sqrt_nonneg R) hphase e he
    (fun i => Real.sqrt (b i))
    (fun i j hij => Real.sqrt_lt_sqrt (hb0 i).le (hb hij))
    (fun i => Real.sqrt_pos.mpr (hb0 i))
    (fun i => Real.sqrt_lt_sqrt (hb0 i).le (hbR i))
  simpa only [translatedU,Real.sq_sqrt (hb0 _).le] using hp

lemma newtonKernel_det_pos_strict {n : ℕ} {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R)
    (hphase : Real.sqrt R*Real.sqrt a < Real.pi/2)
    (b : ℕ → ℝ) (hb : StrictMono (fun i : Fin n => b i))
    (hb0 : ∀ i : Fin n,0 < b i) (hbR : ∀ i : Fin n,b i < R)
    (hball : ∀ i,0 ≤ b i ∧ b i ≤ R) (e : Fin n → ℕ) (he : StrictMono e) :
    0 < Matrix.det (fun i j : Fin n => newtonKernel b (-a) (e i) j) := by
  have hp := translated_beta_eval_det_pos ha hphase (fun i : Fin n => b i) hb hb0 hbR e he
  have hd := cosineKernelJet_det_newton (show 1 ≤ R+1 by linarith)
    (fun i => (abs_le.mpr ⟨by linarith [(hball i).1],by linarith [(hball i).2]⟩ : |b i| ≤ R+1)) (-a) e
  simp only [nodalOrder_eq_zero_strict hb] at hd
  rw [hd] at hp
  exact (mul_pos_iff_of_pos_right (newtonJetMatrix_det_pos b hb.monotone)).mp hp

noncomputable def inwardNodes (n : ℕ) (R : ℝ) (j : ℕ) : ℝ :=
  R*((min j n : ℕ)+1:ℝ)/((n:ℝ)+1)

lemma inwardNodes_pos {R : ℝ} (hR : 0 < R) (n j : ℕ) : 0 < inwardNodes n R j := by
  unfold inwardNodes
  positivity
lemma inwardNodes_le {R : ℝ} (hR : 0 ≤ R) (n j : ℕ) : inwardNodes n R j ≤ R := by
  unfold inwardNodes
  rw [div_le_iff₀ (by positivity)]
  have hm : ((min j n : ℕ):ℝ) ≤ n := by exact_mod_cast min_le_right j n
  nlinarith
lemma inwardNodes_lt {R : ℝ} (hR : 0 < R) {n : ℕ} (j : Fin n) : inwardNodes n R j < R := by
  unfold inwardNodes
  rw [div_lt_iff₀ (by positivity)]
  have hm : ((min j.val n : ℕ):ℝ) < n := by exact_mod_cast (min_le_left j.val n).trans_lt j.isLt
  nlinarith
lemma inwardNodes_strictMono {R : ℝ} (hR : 0 < R) (n : ℕ) :
    StrictMono (fun j : Fin n => inwardNodes n R j) := by
  intro i j hij
  dsimp only [inwardNodes]
  rw [min_eq_left (Nat.le_of_lt i.isLt),min_eq_left (Nat.le_of_lt j.isLt)]
  apply div_lt_div_of_pos_right _ (by positivity)
  apply mul_lt_mul_of_pos_left _ hR
  exact_mod_cast Nat.add_lt_add_right hij 1

noncomputable def inwardPerturb (n : ℕ) (R : ℝ) (b : ℕ → ℝ) (s : ℝ) (j : ℕ) : ℝ :=
  (1-s)*b j+s*inwardNodes n R j

lemma inwardPerturb_range {n : ℕ} {R : ℝ} {b : ℕ → ℝ} (hR : 0 < R)
    (hb : ∀ j,0 ≤ b j ∧ b j ≤ R) {s : ℝ} (hs : s ∈ Icc 0 1) (j : ℕ) :
    0 ≤ inwardPerturb n R b s j ∧ inwardPerturb n R b s j ≤ R := by
  have hv0 := (inwardNodes_pos hR n j).le
  have hvR := inwardNodes_le hR.le n j
  dsimp [inwardPerturb]
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) (hb j).1) (mul_nonneg hs.1 hv0)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (hb j).2),
      mul_nonneg hs.1 (sub_nonneg.mpr hvR)]

lemma inwardPerturb_strict {n : ℕ} {R : ℝ} {b : ℕ → ℝ} (hR : 0 < R)
    (hb : ∀ j,0 ≤ b j ∧ b j ≤ R) (hbmono : Monotone (fun j : Fin n => b j))
    {s : ℝ} (hs : s ∈ Ioc 0 1) :
    StrictMono (fun j : Fin n => inwardPerturb n R b s j) ∧
      (∀ j : Fin n,0 < inwardPerturb n R b s j) ∧
      (∀ j : Fin n,inwardPerturb n R b s j < R) := by
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    have hv := inwardNodes_strictMono hR n hij
    have hb' := hbmono hij.le
    dsimp [inwardPerturb]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hb'),mul_pos hs.1 (sub_pos.mpr hv)]
  · intro j
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hs.2) (hb j).1)
      (mul_pos hs.1 (inwardNodes_pos hR n j))
  · intro j
    have hv := inwardNodes_lt hR j
    dsimp [inwardPerturb]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (hb j).2),mul_pos hs.1 (sub_pos.mpr hv)]

lemma translated_newton_det_nonneg {n : ℕ} {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R)
    (hphase : Real.sqrt R*Real.sqrt a < Real.pi/2) (b : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n => b i)) (hball : ∀ i,0 ≤ b i ∧ b i ≤ R)
    (e : Fin n → ℕ) (he : StrictMono e) :
    0 ≤ Matrix.det (fun i j : Fin n => newtonKernel b (-a) (e i) j) := by
  let f : ℝ → ℝ := fun s => Matrix.det (fun i j : Fin n => newtonKernel (inwardPerturb n R b s) (-a) (e i) j)
  have hc : ContinuousOn f (Icc 0 1) := by
    apply (continuous_id.matrix_det).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    apply continuousOn_newtonKernel (show 1 ≤ R+1 by linarith)
    · exact (show Continuous (inwardPerturb n R b) by unfold inwardPerturb;fun_prop).continuousOn
    · intro s hs k
      have hh := inwardPerturb_range hR hball hs k (n:=n)
      rw [abs_of_nonneg hh.1]
      linarith
  have ht : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)) := by
    have hh := (hc 0 (show (0:ℝ) ∈ Icc 0 1 by norm_num)).mono (show Ioc (0:ℝ) 1 ⊆ Icc 0 1 from fun _ h => ⟨h.1.le,h.2⟩)
    simpa only [ContinuousWithinAt,nhdsWithin_Ioc_eq_nhdsGT (show (0:ℝ) < 1 by norm_num)] using hh
  have hp : ∀ᶠ s in 𝓝[>] (0:ℝ),0 ≤ f s := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with s hs hs1
    have hh := inwardPerturb_strict hR hball hb ⟨hs,hs1.le⟩
    exact (newtonKernel_det_pos_strict ha hR hphase _ hh.1 hh.2.1 hh.2.2
      (inwardPerturb_range hR hball ⟨hs.le,hs1.le⟩) e he).le
  have hh := ge_of_tendsto ht hp
  have hzero : inwardPerturb n R b 0=b := by funext j;simp [inwardPerturb]
  simpa only [f,hzero] using hh

lemma translated_beta_jet_det_nonneg {n : ℕ} {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R)
    (hphase : Real.sqrt R*Real.sqrt a < Real.pi/2) (b : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n => b i)) (hball : ∀ i,0 ≤ b i ∧ b i ≤ R)
    (e : Fin n → ℕ) (he : StrictMono e) :
    0 ≤ Matrix.det (fun i j : Fin n => cosineKernelJet (nodalOrder b j) (e i) (b j) (-a)) := by
  rw [cosineKernelJet_det_newton (show 1 ≤ R+1 by linarith)
    (fun i => (abs_le.mpr ⟨by linarith [(hball i).1],by linarith [(hball i).2]⟩ : |b i| ≤ R+1))]
  exact mul_nonneg (translated_newton_det_nonneg ha hR hphase b hb hball e he)
    (newtonJetMatrix_det_pos b hb).le

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
