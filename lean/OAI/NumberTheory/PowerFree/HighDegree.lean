import OAI.NumberTheory.PowerFree.SurfaceCounting

namespace OAI

namespace QuarticPowerFree

open scoped BigOperators

theorem polynomial_dyadic_eval_bound (f : Polynomial ℤ) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (n : ℤ), 0 ≤ n → (n:ℝ) ≤ 2*X →
      |((f.eval n:ℤ):ℝ)| ≤ C*X^(f.natDegree:ℝ) := by
  classical
  let A : ℝ := ∑ i ∈ f.support, |(f.coeff i:ℝ)|
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let C := 2+A*2^f.natDegree
  have hC : 2 ≤ C := by dsimp [C]; nlinarith [pow_pos (show (0:ℝ)<2 by norm_num) f.natDegree]
  refine ⟨C,hC,fun X hX n hn hnX => ?_⟩
  have hXp : 0 ≤ X := by linarith
  have hn' : 0 ≤ (n:ℝ) := by exact_mod_cast hn
  have hh : |((f.eval n:ℤ):ℝ)| ≤ A*(2*X)^f.natDegree := by
    rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
    push_cast
    calc
      _ ≤ ∑ i ∈ f.support, |(f.coeff i:ℝ)*(n:ℝ)^i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ f.support, |(f.coeff i:ℝ)| *(2*X)^f.natDegree := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul,abs_pow,abs_of_nonneg hn']
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (pow_le_pow_left₀ hn' hnX i).trans (pow_le_pow_right₀ (by linarith)
          (Polynomial.le_natDegree_of_mem_supp i hi))
      _ = A*(2*X)^f.natDegree := by rw [Finset.sum_mul]
  rw [mul_pow] at hh
  rw [Real.rpow_natCast]
  have hc : A*2^f.natDegree ≤ C := by dsimp [C]; linarith
  exact hh.trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hc (pow_nonneg hXp _))

theorem rational_irreducible_squarefree_complex (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    Squarefree (f.map (Int.castRingHom ℂ)) := by
  have h := hf.separable.map (f := Rat.castHom ℂ)
  have he : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by ext; simp
  rw [Polynomial.map_map,he] at h
  exact h.squarefree

theorem rational_irreducible_eval_ne_zero (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 2 ≤ f.natDegree) (n : ℤ) :
    f.eval n ≠ 0 := by
  intro hz
  have hr : (f.map (Int.castRingHom ℚ)).IsRoot (n:ℚ) := by
    change (f.map (Int.castRingHom ℚ)).eval (n:ℚ) = 0
    rw [Polynomial.eval_intCast_map]
    change (Int.castRingHom ℚ) (f.eval n) = 0
    rw [hz,map_zero]
  have hdvd := Polynomial.dvd_iff_isRoot.mpr hr
  have hu : ¬ IsUnit (Polynomial.X-Polynomial.C (n:ℚ)) := by
    exact Polynomial.not_isUnit_of_natDegree_pos _ (by rw [Polynomial.natDegree_X_sub_C]; decide)
  have ha := (hf.dvd_iff.mp hdvd).resolve_left hu
  have he := Polynomial.natDegree_le_of_dvd ha.dvd (Polynomial.X_sub_C_ne_zero (n:ℚ))
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_X_sub_C] at he
  omega

theorem high_degree_two_boxes {C X : ℝ} (hC : 2 ≤ C) (hX : 1 ≤ X)
    {d k : ℕ} (hd : 9 ≤ d) (hk : k = d-2)
    (y : ℤ) (p : ℕ) (hp : X < p)
    (hv : |(y:ℝ)| *(p:ℝ)^k ≤ C*X^(d:ℝ))
    (hy : y ≠ 0) :
    (|(y:ℝ)| ≤ C*X^(2:ℝ) ∧ (p:ℝ) ≤ C*X^(11/10:ℝ)) ∨
    (|(y:ℝ)| ≤ C*X^(13/10:ℝ) ∧ (p:ℝ) ≤ C*X^(13/10:ℝ)) := by
  have hXp : 0 < X := by linarith
  have hpp : (0:ℝ) < p := by linarith
  have hk0 : 0 < k := by omega
  have hkR : (0:ℝ) < k := by exact_mod_cast hk0
  have hdR : (9:ℝ) ≤ d := by exact_mod_cast hd
  have hdk : (d:ℝ) = (k:ℝ)+2 := by exact_mod_cast (show d=k+2 by omega)
  have hy1 : 1 ≤ |(y:ℝ)| := by exact_mod_cast (Int.one_le_abs hy)
  have hCp : 0 < C := by linarith
  have hpow : (p:ℝ)^k ≤ C*X^(d:ℝ) := by nlinarith [pow_pos hpp k]
  have hprime : (p:ℝ) ≤ C*X^(13/10:ℝ) := by
    apply (Real.rpow_le_rpow_iff hpp.le (by positivity) hkR).mp
    simp only [Real.rpow_natCast]
    rw [mul_pow,← Real.rpow_natCast (X^(13/10:ℝ)) k,← Real.rpow_mul hXp.le]
    have hexp : (d:ℝ) ≤ 13/10*(k:ℝ) := by linarith
    have hCC : C ≤ C^k := le_self_pow₀ (by linarith) hk0.ne'
    exact hpow.trans (mul_le_mul hCC (Real.rpow_le_rpow_of_exponent_le hX hexp)
      (Real.rpow_nonneg hXp.le _) (by positivity))
  by_cases hpbox : (p:ℝ) ≤ X^(11/10:ℝ)
  · left
    refine ⟨?_,hpbox.trans (le_mul_of_one_le_left (Real.rpow_nonneg hXp.le _) (by linarith))⟩
    have hxk : X^(k:ℝ) ≤ (p:ℝ)^k := by rw [Real.rpow_natCast]; exact pow_le_pow_left₀ hXp.le hp.le k
    have he : C*X^(d:ℝ) = (C*X^(2:ℝ))*X^(k:ℝ) := by
      rw [hdk,Real.rpow_add hXp]; ring
    have hv' := (mul_le_mul_of_nonneg_left hxk (abs_nonneg (y:ℝ))).trans hv
    rw [he] at hv'
    exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp _)).mp hv'
  · right
    refine ⟨?_,hprime⟩
    have hpbox' : X^(11/10:ℝ) ≤ (p:ℝ) := (lt_of_not_ge hpbox).le
    have hxk : X^((11/10:ℝ)*(k:ℝ)) ≤ (p:ℝ)^k := by
      rw [Real.rpow_mul hXp.le,Real.rpow_natCast]
      exact pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hpbox' k
    have hexp : (d:ℝ) ≤ 13/10+11/10*(k:ℝ) := by linarith
    have he : C*X^(d:ℝ) ≤ (C*X^(13/10:ℝ))*X^((11/10:ℝ)*(k:ℝ)) := by
      rw [mul_assoc,← Real.rpow_add hXp]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hexp) hCp.le
    have hv' := (mul_le_mul_of_nonneg_left hxk (abs_nonneg (y:ℝ))).trans (hv.trans he)
    exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hXp _)).mp hv'

section
open scoped BigOperators Classical

theorem high_degree_selected_count (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 9 ≤ f.natDegree) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin 3 → ℤ),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X) →
      (∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p) →
      (∀ z ∈ S, f.eval (z 0) = z 1*(z 2)^(f.natDegree-2)) →
      (S.card:ℝ) ≤ C*X^(1-1/2000:ℝ) := by
  classical
  let k := f.natDegree-2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hsq := rational_irreducible_squarefree_complex f hirr
  obtain ⟨Cb,hCb,hpoly⟩ := polynomial_dyadic_eval_bound f
  let ω₁ : Fin 3 → ℝ := ![1,2,11/10]
  let ω₂ : Fin 3 → ℝ := ![1,13/10,13/10]
  have hω₁ : ∀ j, 0 < ω₁ j := by intro j; fin_cases j <;> norm_num [ω₁]
  have hω₂ : ∀ j, 0 < ω₂ j := by intro j; fin_cases j <;> norm_num [ω₂]
  have hw₁ : ∀ j, (tripleWeights 10 20 11 j:ℝ) = (10:ℝ)*ω₁ j := by
    intro j; fin_cases j <;> norm_num [tripleWeights,ω₁]
  have hw₂ : ∀ j, (tripleWeights 10 13 13 j:ℝ) = (10:ℝ)*ω₂ j := by
    intro j; fin_cases j <;> norm_num [tripleWeights,ω₂]
  have hd' : (9:ℝ) ≤ f.natDegree := by exact_mod_cast hd
  have hm₁ : (20:ℝ)*11 ≤ (f.natDegree:ℝ)*(10:ℝ)^2*(499/1000:ℝ)^2 := by nlinarith
  have hm₂ : (13:ℝ)*13 ≤ (f.natDegree:ℝ)*(10:ℝ)^2*(499/1000:ℝ)^2 := by nlinarith
  obtain ⟨C₁,X₁,hC₁,hcount₁⟩ := direct_surface_selected_count f hf hsq k hk
    (a := 10) (b := 20) (c := 11) (by norm_num) (by norm_num) (by norm_num)
    ω₁ hω₁ rfl hw₁ (499/1000) (by norm_num) (by norm_num) hm₁ Cb (by linarith)
    (1/2000) (by norm_num)
  obtain ⟨C₂,X₂,hC₂,hcount₂⟩ := direct_surface_selected_count f hf hsq k hk
    (a := 10) (b := 13) (c := 13) (by norm_num) (by norm_num) (by norm_num)
    ω₂ hω₂ rfl hw₂ (499/1000) (by norm_num) (by norm_num) hm₂ Cb (by linarith)
    (1/2000) (by norm_num)
  refine ⟨C₁+C₂,max 1 (max X₁ X₂),by linarith,?_⟩
  intro X hX S hinj hrange hprime heq
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hX₁ : X₁ < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hX
  have hX₂ : X₂ < X := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hX
  let B₁ := fun z : Fin 3 → ℤ => ∀ j, |(z j:ℝ)| ≤ Cb*X^(ω₁ j)
  let B₂ := fun z : Fin 3 → ℤ => ∀ j, |(z j:ℝ)| ≤ Cb*X^(ω₂ j)
  have hcover : ∀ z ∈ S, B₁ z ∨ B₂ z := by
    intro z hz
    obtain ⟨p,hp,hzp,hXp⟩ := hprime z hz
    have hz0 : 0 ≤ z 0 := by exact_mod_cast (show (0:ℝ) ≤ z 0 by linarith [(hrange z hz).1])
    have hb := hpoly X hX1.le (z 0) hz0 (hrange z hz).2
    have hev : ((f.eval (z 0):ℤ):ℝ) = (z 1:ℝ)*(p:ℝ)^k := by
      have hh := congrArg (fun a : ℤ => (a:ℝ)) (heq z hz)
      simpa only [Int.cast_mul,Int.cast_pow,hzp,Int.cast_natCast] using hh
    have hv : |(z 1:ℝ)| *(p:ℝ)^k ≤ Cb*X^(f.natDegree:ℝ) := by
      rw [hev,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ (p:ℝ)^k from pow_nonneg (Nat.cast_nonneg p) k)] at hb
      exact hb
    have hy : z 1 ≠ 0 := by
      intro hy
      have hh := heq z hz
      rw [hy,zero_mul] at hh
      exact rational_irreducible_eval_ne_zero f hirr (by omega) (z 0) hh
    have hb0 : |(z 0:ℝ)| ≤ Cb*X := by
      rw [abs_of_nonneg (by exact_mod_cast hz0)]
      exact (hrange z hz).2.trans (mul_le_mul_of_nonneg_right hCb (by linarith))
    rcases high_degree_two_boxes hCb hX1.le hd rfl (z 1) p hXp hv hy with h₁ | h₂
    · left
      intro j
      fin_cases j
      · simpa [ω₁,Real.rpow_one] using hb0
      · change |(z 1:ℝ)| ≤ Cb*X^(2:ℝ)
        exact h₁.1
      · change |(z 2:ℝ)| ≤ Cb*X^(11/10:ℝ)
        rw [hzp,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg p)]
        exact h₁.2
    · right
      intro j
      fin_cases j
      · simpa [ω₂,Real.rpow_one] using hb0
      · change |(z 1:ℝ)| ≤ Cb*X^(13/10:ℝ)
        exact h₂.1
      · change |(z 2:ℝ)| ≤ Cb*X^(13/10:ℝ)
        rw [hzp,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg p)]
        exact h₂.2
  have hselected : ∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p ∧ (p:ℤ) ∣ f.eval (z 0) := by
    intro z hz
    obtain ⟨p,hp,hzp,hXp⟩ := hprime z hz
    refine ⟨p,hp,hzp,hXp,?_⟩
    rw [heq z hz,hzp]
    exact dvd_mul_of_dvd_right (dvd_pow_self (p:ℤ) (by omega)) _
  have hcomplex : ∀ z ∈ S, (f.map (Int.castRingHom ℂ)).eval (z 0:ℂ) =
      (z 1:ℂ)*(z 2:ℂ)^k := by
    intro z hz
    rw [Polynomial.eval_intCast_map]
    change (((f.eval (z 0):ℤ):ℂ)) = (z 1:ℂ)*(z 2:ℂ)^k
    exact_mod_cast heq z hz
  have hc₁ := hcount₁ X hX₁ (S.filter B₁) (hinj.mono (Finset.filter_subset _ _))
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hrange z (Finset.mem_filter.mp hz).1)
    (fun z hz => hselected z (Finset.mem_filter.mp hz).1)
    (fun z hz => hcomplex z (Finset.mem_filter.mp hz).1)
  have hc₂ := hcount₂ X hX₂ (S.filter B₂) (hinj.mono (Finset.filter_subset _ _))
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hrange z (Finset.mem_filter.mp hz).1)
    (fun z hz => hselected z (Finset.mem_filter.mp hz).1)
    (fun z hz => hcomplex z (Finset.mem_filter.mp hz).1)
  have hsub : S ⊆ (S.filter B₁) ∪ (S.filter B₂) := by
    intro z hz
    rcases hcover z hz with h₁ | h₂
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,h₁⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,h₂⟩)
  have hcard : (S.card:ℝ) ≤ ((S.filter B₁).card:ℝ)+((S.filter B₂).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  norm_num at hc₁ hc₂ ⊢
  nlinarith only [hcard,hc₁,hc₂]

end

open Filter
open scoped Topology Classical

theorem high_degree_dyadic_tail (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 9 ≤ f.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      (dyadicTailCount f (f.natDegree-2) M:ℝ) ≤ C*(M:ℝ)^(1-1/2000:ℝ) := by
  classical
  obtain ⟨C,X₀,hC,hcount⟩ := high_degree_selected_count f hf hirr hd
  refine ⟨C,hC,?_⟩
  have hlim : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_gt_atTop X₀)] with M hM
  let D := (Finset.Ioc M (2*M)).filter fun n : ℕ =>
    ∃ p : ℕ, p.Prime ∧ M < p ∧ (p:ℤ)^(f.natDegree-2) ∣ f.eval (n:ℤ)
  have hD (n : D) : ∃ p : ℕ, p.Prime ∧ M < p ∧
      (p:ℤ)^(f.natDegree-2) ∣ f.eval (n.val:ℤ) := (Finset.mem_filter.mp n.property).2
  choose p hp hMp hdiv using hD
  choose y hy using hdiv
  let z := fun n : D => (![(n.val:ℤ),y n,(p n:ℤ)] : Fin 3 → ℤ)
  have hzinj : Function.Injective z := by
    intro u v huv
    apply Subtype.ext
    have hh := congrFun huv 0
    dsimp only [z,Matrix.cons_val_zero] at hh
    exact_mod_cast hh
  let S := Finset.univ.image z
  have hS : ∀ u ∈ S, ∃ n : D, z n = u := by
    intro u hu
    obtain ⟨n,_,hn⟩ := Finset.mem_image.mp hu
    exact ⟨n,hn⟩
  have hinj : Set.InjOn (fun u : Fin 3 → ℤ => u 0) (S:Set _) := by
    intro u hu v hv huv
    obtain ⟨i,rfl⟩ := hS u hu
    obtain ⟨j,rfl⟩ := hS v hv
    have hij : i = j := by
      apply Subtype.ext
      dsimp only [z,Matrix.cons_val_zero] at huv
      exact_mod_cast huv
    rw [hij]
  have hrange : ∀ u ∈ S, (M:ℝ) < (u 0:ℝ) ∧ (u 0:ℝ) ≤ 2*(M:ℝ) := by
    intro u hu
    obtain ⟨n,rfl⟩ := hS u hu
    have hn := Finset.mem_Ioc.mp (Finset.mem_filter.mp n.property).1
    dsimp only [z,Matrix.cons_val_zero]
    constructor
    · exact_mod_cast hn.1
    · exact_mod_cast hn.2
  have hprime : ∀ u ∈ S, ∃ q : ℕ, q.Prime ∧ u 2 = q ∧ (M:ℝ) < q := by
    intro u hu
    obtain ⟨n,rfl⟩ := hS u hu
    exact ⟨p n,hp n,rfl,by exact_mod_cast hMp n⟩
  have heq : ∀ u ∈ S, f.eval (u 0) = u 1*(u 2)^(f.natDegree-2) := by
    intro u hu
    obtain ⟨n,rfl⟩ := hS u hu
    change f.eval (n.val:ℤ) = y n*(p n:ℤ)^(f.natDegree-2)
    rw [hy n,mul_comm]
  have hc := hcount M hM S hinj hrange hprime heq
  have hcard : S.card = D.card := by
    rw [Finset.card_image_of_injective _ hzinj,Finset.card_univ,Fintype.card_coe]
  simpa only [hcard,dyadicTailCount,D] using hc

theorem density_ge_nine (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 9 ≤ f.natDegree)
    (hlocal : LocallyAdmissible f (f.natDegree-2)) :
    DensityStatement f (f.natDegree-2) := by
  obtain ⟨a,g,ha,hfg,hgprim,_hgpos,hgdeg,hgirr⟩ := exists_primitive_positive_normalization f hirr
  obtain ⟨C,_hC,hbound⟩ := high_degree_dyadic_tail g hgprim hgirr (by omega)
  have ht := dyadic_tail_limit_of_power_saving g (g.natDegree-2) (1/2000) C (by norm_num) hbound
  rw [hgdeg] at ht
  exact densityStatement_from_normalized_dyadic_tail f g hirr (by omega)
    (by omega) hlocal a ha hfg ht

end QuarticPowerFree

end OAI
