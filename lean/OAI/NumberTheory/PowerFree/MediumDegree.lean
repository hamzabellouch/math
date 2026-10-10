import OAI.NumberTheory.PowerFree.EmbeddingCharts

namespace OAI

namespace QuarticPowerFree

section
open NumberField Module MvPolynomial
open scoped Classical BigOperators

theorem norm_indexed_count (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hd : 5 ≤ f.natDegree) (hd' : f.natDegree ≤ 8)
    {K : Type} [Field K] [NumberField K]
    (T : IntegralEmbeddingChart K f.natDegree) (θ : K)
    (hθ : Function.Injective (fun i => T.σ i θ)) (μ : ℕ) (hμ : 0 < μ)
    (Q : Finset (Ideal (𝓞 K))) (hQ : ∀ I ∈ Q, I ≠ ⊥)
    (Cbox : ℝ) (hCbox : 1 ≤ Cbox) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ (ι : Type) [Fintype ι]
      (a : ι → ℤ) (P : ι → ℕ) (J : ι → Ideal (𝓞 K)) (A B : ι → 𝓞 K),
      Function.Injective a →
      (∀ i, X < (a i:ℝ) ∧ (a i:ℝ) ≤ 2*X) →
      (∀ i, J i ∈ Q) →
      (∀ i, (P i).Prime ∧ X < P i ∧ (P i:ℤ) ∣ f.eval (a i)) →
      (∀ i, A i ≠ 0) →
      (∀ i, (A i:K)^(f.natDegree-2)*(B i:K) = (μ:K)*((a i:K)-θ)) →
      (∀ i, |(Algebra.norm ℚ (A i:K):ℝ)| = ((P i*Ideal.absNorm (J i):ℕ):ℝ)) →
      (∀ i j, |(T.coord (A i) j:ℝ)| ≤ Cbox*X^(1/3:ℝ) ∧
        |(T.coord (B i) j:ℝ)| ≤ Cbox*X^(2/5:ℝ)) →
      (Fintype.card ι:ℝ) ≤ C*X^(997/1000:ℝ) := by
  classical
  let M := normBoxOfChart T θ hθ μ hμ (by omega : 0 < f.natDegree)
  let F := Q.card*f.natDegree+1
  obtain ⟨C,X₀,hC,hcount⟩ := norm_box_count hd hd' (by omega : 0 < f.natDegree+1)
    (normBoxWeight f.natDegree) (normBoxWeight_pos _) (normBoxWeight_le _)
    (normBoxNatWeight f.natDegree) (normBoxNatWeight_ne _) (normBoxWeight_scale _)
    M Cbox hCbox F
  refine ⟨C,X₀,hC,fun X hX ι _ a P J A B hainj hrange hJ hP hA he hnorm hbox => ?_⟩
  let z := fun i => normIntegralPoint T (A i) (B i)
  let S := Finset.univ.image z
  have heval (i) : MvPolynomial.aeval (fun j => (z i j:ℂ)) M.q = (a i:ℂ) ∧ PointOn M.ideal (z i) :=
    normIntegralPoint_equation T θ hθ μ hμ _ (A i) (B i) (a i) (he i)
  have hzinj : Function.Injective z := by
    intro i j hij
    apply hainj
    apply Int.cast_injective (α := ℂ)
    rw [←(heval i).1,←(heval j).1,hij]
  have hcard : S.card = Fintype.card ι := by simp only [S,Finset.card_image_of_injective _ hzinj,Finset.card_univ]
  have hb := hcount X hX S
  rw [←hcard]
  apply hb
  · intro v hv j
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    induction j using Fin.addCases with
    | left j => simpa only [z,normIntegralPoint,Fin.addCases_left,normBoxWeight] using (hbox i j).1
    | right j => simpa only [z,normIntegralPoint,Fin.addCases_right,normBoxWeight] using (hbox i j).2
  · intro t
    apply (Finset.card_le_one.mpr ?_).trans (by dsimp [F]; omega)
    intro v hv w hw
    obtain ⟨hvS,hvt⟩ := Finset.mem_filter.mp hv
    obtain ⟨hwS,hwt⟩ := Finset.mem_filter.mp hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hvS
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hwS
    have hij : a i = a j := Int.cast_injective (α := ℂ) ((heval i).1.symm.trans
      ((hvt.trans hwt.symm).trans (heval j).1))
    rw [hainj hij]
  · intro c
    let R := Finset.univ.filter (fun i => ∀ j, z i (Fin.castAdd f.natDegree j) = c j)
    have hsubset : S.filter (fun v => ∀ j, v (M.x j) = c j) ⊆ R.image z := by
      intro v hv
      obtain ⟨hvS,hvc⟩ := Finset.mem_filter.mp hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hvS
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hvc⟩,rfl⟩
    apply ((Finset.card_le_card hsubset).trans (Finset.card_image_le)).trans
    by_cases hR : R.Nonempty
    · obtain ⟨i₀,hi₀⟩ := hR
      have hRsub : R ⊆ Finset.univ.filter (fun i => A i=A i₀) := by
        intro i hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,T.B.repr.injective ?_⟩
        ext j
        have h₁ := (Finset.mem_filter.mp hi).2 j
        have h₂ := (Finset.mem_filter.mp hi₀).2 j
        simpa only [z,normIntegralPoint,Fin.addCases_left,IntegralEmbeddingChart.coord] using h₁.trans h₂.symm
      have hc := norm_left_fibre_count f hf Finset.univ a hainj.injOn X
        (fun i _ => hrange i) P J A Q hQ (fun i _ => hJ i) (fun i _ => hP i)
        (fun i _ => hnorm i) (A i₀)
      exact ((Finset.card_le_card hRsub).trans hc).trans (by dsimp [F]; omega)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hR,Finset.card_empty]
      exact Nat.zero_le _
  · intro v hv j
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    change MvPolynomial.aeval (fun l => (z i l:ℂ)) (coordinateLinearForm (Fin.castAdd f.natDegree) (T.A j)) ≠ 0
    rw [normIntegralPoint_left]
    apply (map_ne_zero (T.σ j)).mpr
    exact_mod_cast hA i
  · intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    exact (heval i).2

end

section

theorem norm_onebox_exponents {d p : ℕ} (hd : 5 ≤ d) {F X : ℝ}
    (hF : 1 ≤ F) (hX : 1 ≤ X) (hp : X < p)
    (hv : (p:ℝ)^(d-2) ≤ F*X^(d:ℝ)) :
    (p:ℝ)^((d:ℝ)⁻¹) ≤ F*X^(1/3:ℝ) ∧
      X/(p:ℝ)^((d:ℝ)⁻¹*(d-2:ℕ)) ≤ X^(2/5:ℝ) := by
  let k := d-2
  have hdR : (5:ℝ) ≤ d := by exact_mod_cast hd
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by dsimp [k]; omega)
  have hdk : (d:ℝ) = (k:ℝ)+2 := by exact_mod_cast (show d=k+2 by dsimp [k]; omega)
  have hd0 : (0:ℝ) < d := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hXp : 0 < X := by linarith
  have hpp : (0:ℝ) < p := by linarith
  have hFp : 0 < F := by linarith
  constructor
  · apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hpp.le _) (by positivity) (mul_pos hd0 hk0)).mp
    rw [←Real.rpow_mul hpp.le,show (d:ℝ)⁻¹*((d:ℝ)*k) = k by field_simp,
      Real.rpow_natCast,Real.mul_rpow hFp.le (Real.rpow_nonneg hXp.le _),←Real.rpow_mul hXp.le]
    have hFk : F ≤ F^((d:ℝ)*k) := by
      have hh : (1:ℝ) ≤ (d:ℝ)*k := by nlinarith
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hF hh
    have he : (d:ℝ) ≤ 1/3*((d:ℝ)*k) := by nlinarith
    exact hv.trans (mul_le_mul hFk (Real.rpow_le_rpow_of_exponent_le hX he)
      (Real.rpow_nonneg hXp.le _) (by positivity))
  · have hek : 0 ≤ (d:ℝ)⁻¹*(k:ℝ) := by positivity
    have hpw := Real.rpow_le_rpow hXp.le hp.le hek
    have he : 1-(d:ℝ)⁻¹*(k:ℝ) ≤ 2/5 := by
      rw [inv_mul_eq_div]
      have hh : (3/5:ℝ) ≤ (k:ℝ)/(d:ℝ) := (le_div_iff₀ hd0).mpr (by linarith)
      linarith
    calc
      X/(p:ℝ)^((d:ℝ)⁻¹*(d-2:ℕ)) ≤ X/X^((d:ℝ)⁻¹*k) :=
        div_le_div_of_nonneg_left hXp.le (Real.rpow_pos_of_pos hXp _) hpw
      _ = X^(1-(d:ℝ)⁻¹*k) := by rw [Real.rpow_sub hXp,Real.rpow_one]
      _ ≤ X^(2/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hX he

open NumberField Module
open scoped Classical BigOperators

theorem balanced_coordinates_onebox {K : Type} [Field K] [NumberField K] {d : ℕ}
    (hd : 5 ≤ d) (T : IntegralEmbeddingChart K d) (μ : ℕ) (hμ : 0 < μ)
    (C F : ℝ) (hC : 1 ≤ C) (hF : 1 ≤ F) :
    ∃ Cbox : ℝ, 1 ≤ Cbox ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (p : ℕ), X < p →
      (p:ℝ)^(d-2) ≤ F*X^(d:ℝ) → ∀ α β : 𝓞 K,
      (∀ w : InfinitePlace K, w (α:K) ≤ C*(p:ℝ)^((d:ℝ)⁻¹) ∧
        w ((β:K)/(μ:K)) ≤ (3*C^(d-2))*(X/(p:ℝ)^((d:ℝ)⁻¹*(d-2:ℕ)))) →
      ∀ j, |(T.coord α j:ℝ)| ≤ Cbox*X^(1/3:ℝ) ∧
        |(T.coord β j:ℝ)| ≤ Cbox*X^(2/5:ℝ) := by
  obtain ⟨E,hE,hbound⟩ := T.coordinates_bound
  let Ca := E*(C*F)
  let Cb := E*((μ:ℝ)*(3*C^(d-2)))
  let Cbox := 1+Ca+Cb
  have hCp : 0 ≤ C := by linarith
  have hFp : 0 ≤ F := by linarith
  have hEp : 0 ≤ E := by linarith
  have hCa : 0 ≤ Ca := mul_nonneg hEp (mul_nonneg hCp hFp)
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  have haC : Ca ≤ Cbox := by dsimp [Cbox]; linarith
  have hbC : Cb ≤ Cbox := by dsimp [Cbox]; linarith
  refine ⟨Cbox,by dsimp [Cbox]; linarith,fun X hX p hp hv α β harch j => ?_⟩
  have hXp : 0 < X := by linarith
  have hab := norm_onebox_exponents hd hF hX hp hv
  have hα (i) : ‖T.σ i (α:K)‖ ≤ (C*F)*X^(1/3:ℝ) := by
    have hh := (harch (InfinitePlace.mk (T.σ i))).1
    rw [InfinitePlace.apply] at hh
    exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hab.1 hCp)
  have hβ (i) : ‖T.σ i (β:K)‖ ≤ ((μ:ℝ)*(3*C^(d-2)))*X^(2/5:ℝ) := by
    have hh := (harch (InfinitePlace.mk (T.σ i))).2
    simp only [InfinitePlace.apply,map_div₀,map_natCast,Complex.norm_natCast] at hh
    have hμR : (0:ℝ) < μ := by exact_mod_cast hμ
    have ht : ‖T.σ i (β:K)‖/(μ:ℝ) ≤ (3*C^(d-2))*X^(2/5:ℝ) :=
      hh.trans (mul_le_mul_of_nonneg_left hab.2 (by positivity))
    have hh' := (div_le_iff₀ hμR).mp ht
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh'
  constructor
  · have hh := hbound α ((C*F)*X^(1/3:ℝ)) (by positivity) hα j
    exact hh.trans (by simpa only [Ca,mul_assoc] using mul_le_mul_of_nonneg_right haC (Real.rpow_nonneg hXp.le (1/3)))
  · have hh := hbound β (((μ:ℝ)*(3*C^(d-2)))*X^(2/5:ℝ)) (by positivity) hβ j
    exact hh.trans (by simpa only [Cb,mul_assoc] using mul_le_mul_of_nonneg_right hbC (Real.rpow_nonneg hXp.le (2/5)))

theorem large_prime_power_upper (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 2 ≤ f.natDegree)
    (D X : ℝ) (n : ℤ) (p k : ℕ)
    (hb : |((f.eval n:ℤ):ℝ)| ≤ D*X^(f.natDegree:ℝ))
    (hdiv : (p:ℤ)^k ∣ f.eval n) : (p:ℝ)^k ≤ D*X^(f.natDegree:ℝ) := by
  have hh := Int.natAbs_le_of_dvd_ne_zero hdiv (rational_irreducible_eval_ne_zero f hf hd n)
  have hh' : (p:ℝ)^k ≤ |((f.eval n:ℤ):ℝ)| := by
    have hn : (p:ℝ)^k ≤ ((f.eval n).natAbs:ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hn
  exact hh'.trans hb

end

section
open Filter NumberField
open scoped Topology Classical

theorem medium_degree_dyadic_tail (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hc : 0 < f.leadingCoeff)
    (hd : 5 ≤ f.natDegree) (hd' : f.natDegree ≤ 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (dyadicTailCount f (f.natDegree-2) N:ℝ) ≤ C*(N:ℝ)^(1-3/1000:ℝ) := by
  classical
  obtain ⟨M,μ,Q,C,Xcut,hμ,hC,_hXcut,hQ,hfactor⟩ :=
    balanced_arithmetic f hirr (by omega) hc (f.natDegree-2) (by omega)
  obtain ⟨F,hF,heval⟩ := polynomial_dyadic_eval_bound f
  let T := integralEmbeddingChart M.Carrier f.natDegree M.degree_eq
  have hθ := arithmeticModel_distinct f M T.σ
  obtain ⟨Cbox,hCbox,hbox⟩ := balanced_coordinates_onebox hd T μ hμ C F hC (by linarith)
  obtain ⟨D,Xcount,hD,hcount⟩ := norm_indexed_count f hf hd hd' T M.root hθ μ hμ Q hQ Cbox hCbox
  refine ⟨D,hD,?_⟩
  have hlim : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_gt_atTop (max 1 (max Xcut Xcount)))] with N hN
  have hN1 : 1 ≤ (N:ℝ) := (le_max_left _ _).trans hN.le
  have hNcut : Xcut ≤ (N:ℝ) := (le_max_left _ _).trans (le_max_right _ _) |>.trans hN.le
  have hNcount : Xcount < (N:ℝ) := (le_max_right _ _).trans (le_max_right _ _) |>.trans_lt hN
  let S := (Finset.Ioc N (2*N)).filter fun n : ℕ =>
    ∃ p : ℕ, p.Prime ∧ N < p ∧ (p:ℤ)^(f.natDegree-2) ∣ f.eval (n:ℤ)
  have hS (n : S) : ∃ p : ℕ, p.Prime ∧ N < p ∧
      (p:ℤ)^(f.natDegree-2) ∣ f.eval (n.val:ℤ) := (Finset.mem_filter.mp n.property).2
  choose P hP hNP hdiv using hS
  have hrange (n : S) : (N:ℝ) < (n.val:ℝ) ∧ (n.val:ℝ) ≤ 2*(N:ℝ) := by
    have hn := Finset.mem_Ioc.mp (Finset.mem_filter.mp n.property).1
    constructor
    · exact_mod_cast hn.1
    · exact_mod_cast hn.2
  have hNP' (n : S) : (N:ℝ) < P n := by exact_mod_cast hNP n
  have hfac (n : S) := (hfactor N hNcut (n.val:ℤ) (P n)
    (by exact_mod_cast (hrange n).1) (by exact_mod_cast (hrange n).2)
    (hP n) (hNP' n) (hdiv n)).2
  choose J hJ A hA B hAB hnorm harch using hfac
  have hcoords (n : S) (j) : |(T.coord (A n) j:ℝ)| ≤ Cbox*(N:ℝ)^(1/3:ℝ) ∧
      |(T.coord (B n) j:ℝ)| ≤ Cbox*(N:ℝ)^(2/5:ℝ) := by
    apply hbox N hN1 (P n) (hNP' n) _ (A n) (B n) (fun w => ⟨(harch n w).1.2,(harch n w).2.2⟩) j
    apply large_prime_power_upper f hirr (by omega) F N (n.val:ℤ) (P n) (f.natDegree-2) _ (hdiv n)
    exact heval N hN1 (n.val:ℤ) (by positivity) (by exact_mod_cast (hrange n).2)
  have hprime (n : S) : (P n).Prime ∧ (N:ℝ) < P n ∧ (P n:ℤ) ∣ f.eval (n.val:ℤ) := by
    refine ⟨hP n,hNP' n,?_⟩
    exact dvd_trans (dvd_pow_self _ (by omega : f.natDegree-2 ≠ 0)) (hdiv n)
  have hninj : Function.Injective (fun n : S => (n.val:ℤ)) := by
    intro n m h
    apply Subtype.ext
    exact Int.natCast_inj.mp h
  have hh := hcount N hNcount S (fun n => (n.val:ℤ)) P J A B hninj
    (fun n => by simpa only [Int.cast_natCast] using hrange n) hJ hprime hA hAB hnorm hcoords
  norm_num only [show (1-3/1000:ℝ) = 997/1000 by norm_num]
  simpa only [Fintype.card_coe,dyadicTailCount,S] using hh

theorem density_ge_five (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 5 ≤ f.natDegree)
    (hlocal : LocallyAdmissible f (f.natDegree-2)) :
    DensityStatement f (f.natDegree-2) := by
  by_cases hd9 : 9 ≤ f.natDegree
  · exact density_ge_nine f hirr hd9 hlocal
  obtain ⟨a,g,ha,hfg,hgprim,hgpos,hgdeg,hgirr⟩ := exists_primitive_positive_normalization f hirr
  obtain ⟨C,_hC,hbound⟩ := medium_degree_dyadic_tail g hgprim hgirr hgpos (by omega) (by omega)
  have ht := dyadic_tail_limit_of_power_saving g (g.natDegree-2) (3/1000) C (by norm_num) hbound
  rw [hgdeg] at ht
  exact densityStatement_from_normalized_dyadic_tail f g hirr (by omega)
    (by omega) hlocal a ha hfg ht

end

open MvPolynomial
open scoped Classical BigOperators

structure QuarticBoxSystem (n D A B : ℕ) (U : ℝ) (ω : Fin n → ℝ) (w : Fin n → ℕ) where
  Carrier : Type
  [field : Field Carrier]
  [charZero : CharZero Carrier]
  v : Fin 4 → Carrier
  independent : LinearIndependent ℚ v
  σ : Fin 4 → Carrier →+* ℂ
  θ : Fin 4 → ℂ
  distinct : Function.Injective θ
  x : Fin 4 → Fin n
  xweight : ∀ i, ω (x i) = U
  b : Fin 4 → MvPolynomial (Fin n) ℂ
  q : MvPolynomial (Fin n) ℂ
  generates : Algebra.adjoin ℂ
    (Set.range (fun i => coordinateLinearForm x (σ i ∘ v)) ∪ Set.range b) = ⊤
  leftDegree : ∀ i, (coordinateLinearForm x (σ i ∘ v)).totalDegree ≤ D
  qDegree : q.totalDegree ≤ D
  leftWeight : ∀ i, coordinateLinearForm x (σ i ∘ v) ∈ weightedSpace w A
  rightWeight : ∀ i, b i ∈ weightedSpace w B
attribute [instance] QuarticBoxSystem.field QuarticBoxSystem.charZero

noncomputable def QuarticBoxSystem.a {n D A B : ℕ} {U : ℝ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : QuarticBoxSystem n D A B U ω w) (i : Fin 4) : MvPolynomial (Fin n) ℂ :=
  coordinateLinearForm M.x (M.σ i ∘ M.v)
noncomputable def QuarticBoxSystem.equation {n D A B : ℕ} {U : ℝ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : QuarticBoxSystem n D A B U ω w) (i : Fin 4) : MvPolynomial (Fin n) ℂ := M.a i^2*M.b i-M.q+C (M.θ i)
noncomputable def QuarticBoxSystem.ideal {n D A B : ℕ} {U : ℝ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : QuarticBoxSystem n D A B U ω w) : Ideal (MvPolynomial (Fin n) ℂ) := Ideal.span (Set.range M.equation)

theorem QuarticBoxSystem.quotient_equations {n D A B : ℕ} {U : ℝ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : QuarticBoxSystem n D A B U ω w) (I : Ideal (MvPolynomial (Fin n) ℂ)) (hI : M.ideal ≤ I) :
    ∀ i, Ideal.Quotient.mk I (M.a i)^2*Ideal.Quotient.mk I (M.b i) =
      Ideal.Quotient.mk I M.q-algebraMap ℂ _ (M.θ i) := by
  intro i
  have hm : M.equation i ∈ I := hI (Ideal.subset_span ⟨i,rfl⟩)
  have he := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
  simp only [QuarticBoxSystem.equation,map_add,map_sub,map_mul,map_pow] at he
  change Ideal.Quotient.mk I (M.a i)^2*Ideal.Quotient.mk I (M.b i)-
    Ideal.Quotient.mk I M.q+algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) (M.θ i) = 0 at he
  linear_combination he

theorem QuarticBoxSystem.quotient_left_nonzero {n D A B : ℕ} {U : ℝ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : QuarticBoxSystem n D A B U ω w) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (z : Fin n → ℤ) (hz : PointOn I z)
    (ha : ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) :
    ∀ i, Ideal.Quotient.mk I (M.a i) ≠ 0 := by
  intro i hi
  have hh := congrArg (pointEvaluation I z hz) hi
  rw [map_zero] at hh
  change MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) = 0 at hh
  exact ha i hh

theorem QuarticBoxSystem.right_real_weight {n D A B : ℕ} {U : ℝ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : QuarticBoxSystem n D A B U ω w) (hω : ∀ i, 0 < ω i)
    (L V : ℝ) (hL : 0 < L) (hV : 0 ≤ V) (hB : (B:ℝ)=L*V)
    (hscale : ∀ i, (w i:ℝ) = L*ω i) (I : Ideal (MvPolynomial (Fin n) ℂ)) (i : Fin 4) :
    Ideal.Quotient.mk I (M.b i) ∈ weightedFunctions I ω V := by
  have hh := weightedSpace_map_le_weightedFunctions I w ω hω L hL hscale V hV
  rw [←hB,Nat.floor_natCast] at hh
  exact hh ⟨M.b i,M.rightWeight i,rfl⟩

end QuarticPowerFree

end OAI
