import OAI.NumberTheory.DirichletL.Moments.CommonRadialData

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadialCost
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentAllocationCost
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma sqrt_nat_le_add_one (n:ℕ) : Real.sqrt (n:ℝ)≤(n:ℝ)+1 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]

omit [DecidableEq ι] in
 theorem paired_card_subpower (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι) (C D:Ideal O),C≠0 → D≠0 →
      ∀Z:ℝ,1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      (Real.sqrt ((actualAllocations s.pools C).card:ℝ)*Real.sqrt ((actualAllocations s.pools D).card:ℝ))*
        (((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ))≤C0*Z^δ := by
  let ε:ℝ:=δ/(4*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  obtain ⟨D0,hD0,hcard⟩:=actualAllocations_uniform_small_power (Fintype.card (ι⊕Fin 2)) ε hε
  refine ⟨(D0+1)^4,by positivity,?_⟩
  intro s C D hC hD Z hZ hNC hND
  have hz:0<Z:=zero_lt_one.trans hZ
  have bound (I:Ideal O) (hI:I≠0) (hn:(Ideal.absNorm I:ℝ)≤Z^B):
      ((actualAllocations s.pools I).card:ℝ)+1≤(D0+1)*Z^(B*ε):=by
    have hi:(1:ℝ)≤Ideal.absNorm I:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have hh:=hcard (le_refl (Fintype.card (ι⊕Fin 2))) s.pools I hI
    have hp:(Ideal.absNorm I:ℝ)^ε≤Z^(B*ε):=by
      apply (Real.rpow_le_rpow (by positivity) hn hε.le).trans_eq
      rw [←Real.rpow_mul hz.le]
    have hone:1≤Z^(B*ε):=Real.one_le_rpow hZ.le (mul_nonneg hB hε.le)
    nlinarith [mul_le_mul_of_nonneg_left hp hD0.le]
  have hc:=bound C hC hNC
  have hd:=bound D hD hND
  have hSc:Real.sqrt ((actualAllocations s.pools C).card:ℝ)≤(D0+1)*Z^(B*ε):=
    (sqrt_nat_le_add_one _).trans hc
  have hSd:Real.sqrt ((actualAllocations s.pools D).card:ℝ)≤(D0+1)*Z^(B*ε):=
    (sqrt_nat_le_add_one _).trans hd
  have hcc:((actualAllocations s.pools C).card:ℝ)≤(D0+1)*Z^(B*ε):=by linarith
  have hdd:((actualAllocations s.pools D).card:ℝ)≤(D0+1)*Z^(B*ε):=by linarith
  calc
    _≤(((D0+1)*Z^(B*ε))*((D0+1)*Z^(B*ε)))*
        (((D0+1)*Z^(B*ε))*((D0+1)*Z^(B*ε))):=by gcongr
    _=(D0+1)^4*Z^(4*B*ε):=by
      rw [show ((D0+1)*Z^(B*ε)*((D0+1)*Z^(B*ε)))*
        ((D0+1)*Z^(B*ε)*((D0+1)*Z^(B*ε)))=(D0+1)^4*(Z^(B*ε))^4 by ring]
      rw [←Real.rpow_mul_natCast hz.le]
      congr 2
      ring
    _≤_:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have he:ε*(4*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
      nlinarith

omit [DecidableEq ι] in
 theorem card_squared_subpower (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι) (C:Ideal O),C≠0 →
      ∀Z:ℝ,1<Z → (Ideal.absNorm C:ℝ)≤Z^B →
      ((actualAllocations s.pools C).card:ℝ)^2≤C0*Z^δ := by
  obtain ⟨C0,hC0,hbound⟩:=paired_card_subpower (ι:=ι) B δ hB hδ
  refine ⟨C0,hC0,?_⟩
  intro s C hC Z hZ hn
  have hh:=hbound s C C hC hC Z hZ hn hn
  have he:Real.sqrt ((actualAllocations s.pools C).card:ℝ)*
      Real.sqrt ((actualAllocations s.pools C).card:ℝ)=((actualAllocations s.pools C).card:ℝ):=by
    rw [←pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [he] at hh
  by_cases hz:(actualAllocations s.pools C).card=0
  · rw [hz,Nat.cast_zero,zero_pow (by decide)]
    positivity
  · have hc:(1:ℝ)≤(actualAllocations s.pools C).card:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    apply le_trans ?_ hh
    nlinarith [sq_nonneg ((actualAllocations s.pools C).card:ℝ)]

end SevenEighths.CenteredMomentCommonRadialCost

end

end OAI
