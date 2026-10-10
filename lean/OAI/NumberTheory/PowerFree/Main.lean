import OAI.NumberTheory.PowerFree.RadialFibres

namespace OAI

namespace QuarticPowerFree

section
open Filter NumberField
open scoped Topology Classical BigOperators

theorem indexed_card_le_sum_fibres {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → κ) : Fintype.card ι ≤ ∑ j : κ, (Finset.univ.filter (fun i => b i=j)).card := by
  classical
  let R (j : κ) := Finset.univ.filter (fun i => b i=j)
  have hcover : (Finset.univ : Finset ι) ⊆ Finset.univ.biUnion R := by
    intro i _
    exact Finset.mem_biUnion.mpr ⟨b i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  simpa only [Finset.card_univ] using (Finset.card_le_card hcover).trans Finset.card_biUnion_le

theorem quartic_dyadic_tail (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hc : 0 < f.leadingCoeff)
    (hd : f.natDegree=4) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (dyadicTailCount f (f.natDegree-2) N:ℝ) ≤ C*(N:ℝ)^(1-3/1000:ℝ) := by
  classical
  obtain ⟨M,μ,Q,C,Xcut,hμ,hC,_hXcut,hQ,hfactor⟩ :=
    balanced_arithmetic f hirr (by omega) hc (f.natDegree-2) (by omega)
  obtain ⟨F,hF,heval⟩ := polynomial_dyadic_eval_bound f
  have hK : Module.finrank ℚ M.Carrier=4 := M.degree_eq.trans hd
  let T := integralEmbeddingChart M.Carrier 4 hK
  have hθ : Function.Injective (fun i => T.σ i M.root) := by
    intro i j hij
    apply T.σ.injective
    apply (RingHom.equivRatAlgHom M.Carrier ℂ).injective
    apply M.powerBasis.algHom_ext
    change T.σ i M.powerBasis.gen = T.σ j M.powerBasis.gen
    rw [M.powerBasis_gen,M.integralRoot_eq]
    simp only [map_mul,map_intCast,hij]
  have hboxes (j : Fin 100) := balanced_coordinates_quarticbox j T μ hμ C F hC (by linarith)
  choose Cbox hCbox hbox using hboxes
  have hcounts (j : Fin 100) := quartic_indexed_count f hf hd j hK T M.root hθ μ hμ Q hQ (Cbox j) (hCbox j)
  choose D Xcount hD hcount using hcounts
  let Dall : ℝ := ∑ j : Fin 100, D j
  have hDall : 0 < Dall := Finset.sum_pos (fun j _ => hD j) Finset.univ_nonempty
  refine ⟨Dall,hDall,?_⟩
  have hlim : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hall : ∀ᶠ N : ℕ in atTop, ∀ j : Fin 100, Xcount j < (N:ℝ) :=
    Filter.eventually_all.mpr (fun j => hlim.eventually (eventually_gt_atTop (Xcount j)))
  filter_upwards [hlim.eventually (eventually_gt_atTop (max 1 Xcut)),hall] with N hN hNcount
  have hN1 : 1 ≤ (N:ℝ) := (le_max_left _ _).trans hN.le
  have hNcut : Xcut ≤ (N:ℝ) := (le_max_right _ _).trans hN.le
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
  have hprime (n : S) : (P n).Prime ∧ (N:ℝ) < P n ∧ (P n:ℤ) ∣ f.eval (n.val:ℤ) := by
    refine ⟨hP n,hNP' n,?_⟩
    exact dvd_trans (dvd_pow_self _ (by omega : f.natDegree-2 ≠ 0)) (hdiv n)
  have hupper (n : S) : (P n:ℝ) ≤ F*(N:ℝ)^2 := by
    have hp2 := large_prime_power_upper f hirr (by omega) F N (n.val:ℤ) (P n) (f.natDegree-2)
      (heval N hN1 (n.val:ℤ) (by positivity) (by exact_mod_cast (hrange n).2)) (hdiv n)
    rw [hd] at hp2
    simp only [Nat.reduceSub,Real.rpow_natCast] at hp2
    change (P n:ℝ)^2 ≤ F*(N:ℝ)^(4:ℕ) at hp2
    apply (sq_le_sq₀ (by positivity : (0:ℝ) ≤ P n) (by positivity : 0 ≤ F*(N:ℝ)^2)).mp
    have hFF : F ≤ F^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hFF (sq_nonneg ((N:ℝ)^2))
    nlinarith only [hp2,hh]
  have hbins (n : S) := quartic_prime_bin N F (P n) hN1 (by linarith) (hNP' n) (hupper n)
  choose bin hbinlo hbinhi using hbins
  let R (j : Fin 100) := Finset.univ.filter (fun n : S => bin n=j)
  have hR (j : Fin 100) : ((R j).card:ℝ) ≤ D j*(N:ℝ)^(997/1000:ℝ) := by
    let a : R j → ℤ := fun n => (n.val.val:ℤ)
    have hainj : Function.Injective a := by
      intro n m he
      apply Subtype.ext
      apply Subtype.ext
      exact Int.natCast_inj.mp he
    have hbe (n : R j) : bin n.val=j := (Finset.mem_filter.mp n.property).2
    have hcoords (n : R j) (i) : |(T.coord (A n.val) i:ℝ)| ≤ Cbox j*(N:ℝ)^(quarticU j) ∧
        |(T.coord (B n.val) i:ℝ)| ≤ Cbox j*(N:ℝ)^(quarticV j) := by
      have hlo : (N:ℝ)^(quarticLowerEta j) < P n.val := by simpa only [hbe n] using hbinlo n.val
      have hhi : (P n.val:ℝ) ≤ F*(N:ℝ)^(quarticUpperEta j) := by simpa only [hbe n] using hbinhi n.val
      apply hbox j N hN1 (P n.val) hlo hhi (A n.val) (B n.val) ?_ i
      intro w
      have hh := And.intro (harch n.val w).1.2 (harch n.val w).2.2
      simpa only [hd,Nat.reduceSub,Nat.cast_ofNat] using hh
    have hh := hcount j N (hNcount j) (R j) a (fun n => P n.val) (fun n => J n.val)
      (fun n => A n.val) (fun n => B n.val) hainj
      (fun n => by simpa only [a,Int.cast_natCast] using hrange n.val)
      (fun n => hJ n.val) (fun n => hprime n.val) (fun n => hA n.val)
      (fun n => by simpa only [hd,Nat.reduceSub] using hAB n.val)
      (fun n => hnorm n.val) hcoords
    simpa only [Fintype.card_coe] using hh
  have hcard : (S.card:ℝ) ≤ ∑ j : Fin 100, ((R j).card:ℝ) := by
    have hh := (Nat.cast_le (α := ℝ)).mpr (indexed_card_le_sum_fibres bin)
    simp only [Fintype.card_coe,Nat.cast_sum] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    ext n
    simp only [R,Finset.mem_filter,Finset.mem_univ,true_and]
  calc
    (dyadicTailCount f (f.natDegree-2) N:ℝ) = (S.card:ℝ) := rfl
    _ ≤ ∑ j : Fin 100, ((R j).card:ℝ) := hcard
    _ ≤ ∑ j : Fin 100, D j*(N:ℝ)^(997/1000:ℝ) := Finset.sum_le_sum (fun j _ => hR j)
    _ = Dall*(N:ℝ)^(1-3/1000:ℝ) := by rw [←Finset.sum_mul]; norm_num only [show (1-3/1000:ℝ)=997/1000 by norm_num]; rfl

end

theorem density_ge_four (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 4 ≤ f.natDegree)
    (hlocal : LocallyAdmissible f (f.natDegree-2)) :
    DensityStatement f (f.natDegree-2) := by
  by_cases hd5 : 5 ≤ f.natDegree
  · exact density_ge_five f hirr hd5 hlocal
  obtain ⟨a,g,ha,hfg,hgprim,hgpos,hgdeg,hgirr⟩ := exists_primitive_positive_normalization f hirr
  obtain ⟨C,_hC,hbound⟩ := quartic_dyadic_tail g hgprim hgirr hgpos (by omega)
  have ht := dyadic_tail_limit_of_power_saving g (g.natDegree-2) (3/1000) C (by norm_num) hbound
  rw [hgdeg] at ht
  exact densityStatement_from_normalized_dyadic_tail f g hirr (by omega)
    (by omega) hlocal a ha hfg ht

theorem density (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdeglo : 4 ≤ f.natDegree) (hdeghi : f.natDegree ≤ 8)
    (hlocal : LocallyAdmissible f (f.natDegree - 2)) :
    DensityStatement f (f.natDegree - 2) := by
  have _ := hdeghi
  exact density_ge_four f hirr hdeglo hlocal

theorem allDegrees (f : Polynomial ℤ)
    (hirr : Irreducible (f.map (Int.castRingHom ℚ)))
    (hdeglo : 4 ≤ f.natDegree)
    (hlocal : LocallyAdmissible f (f.natDegree - 2)) :
    DensityStatement f (f.natDegree - 2) := by
  exact density_ge_four f hirr hdeglo hlocal

end QuarticPowerFree

end OAI
