import OAI.Combinatorics.ThinTrees.Capture

namespace OAI

universe uT uE uI uI2 uA uB

section
open scoped Classical
open Matrix

namespace StrongThinTree.BagDensity
noncomputable section
open Finset
open scoped Classical
variable {T : Type uT} {E : Type uE} [DecidableEq E]

omit [DecidableEq E] in
lemma sum_square_bound (F : Finset E) (a : E → ℝ) {c : ℝ}
    (hc : ∀e ∈ F, (a e)^2 ≤ c) : (∑e ∈ F, a e)^2 ≤ c*(F.card : ℝ)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F (fun _ => (1:ℝ)) a
  have hs : (∑e ∈ F, (a e)^2) ≤ (F.card : ℝ)*c := by simpa using sum_le_sum hc
  simp only [one_pow,sum_const,nsmul_eq_mul,mul_one,one_mul] at hcs
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg F.card : (0:ℝ) ≤ _)
  nlinarith

omit [DecidableEq E] in
lemma local_density (O F : Finset E) (a d : E → ℝ) {α γ c₁ c₂ : ℝ}
    (hF : F ⊆ O) (hFn : F.Nonempty) (hα : 0 < α) (hγ : 0 < γ)
    (hd : ∀e ∈ O, 0 ≤ d e) (hmax : ∀e ∈ F, (a e)^2 ≤ 4*c₁)
    (hmin : ∀e ∈ F, c₂/4 ≤ d e)
    (hbad : α*(O.card : ℝ)*(∑e ∈ O, d e) ≤ (∑e ∈ O, a e)^2)
    (hdom : γ*(∑e ∈ O, a e)^2 ≤ (∑e ∈ F, a e)^2) :
    α*γ*(O.card : ℝ)*c₂ ≤ 16*c₁*F.card := by
  have hFc : (0:ℝ) < F.card := by exact_mod_cast card_pos.mpr hFn
  have hOc : (0:ℝ) ≤ O.card := Nat.cast_nonneg _
  have hsum : (F.card : ℝ)*(c₂/4) ≤ ∑e ∈ O, d e := by
    calc
      _ = ∑_e ∈ F, c₂/4 := by simp
      _ ≤ ∑e ∈ F, d e := sum_le_sum hmin
      _ ≤ ∑e ∈ O, d e := sum_le_sum_of_subset_of_nonneg hF (fun e he _ => hd e he)
  have hh1 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ γ*α*(O.card : ℝ) by positivity)
  have hh2 := mul_le_mul_of_nonneg_left hbad hγ.le
  have hu := sum_square_bound F a hmax
  apply (mul_le_mul_iff_right₀ hFc).mp
  nlinarith

lemma family_density (Ts : Finset T) (O F : T → Finset E) (a d : E → ℝ)
    {α γ c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hc : 0 ≤ c₁)
    (hF : ∀t ∈ Ts, F t ⊆ O t) (hFn : ∀t ∈ Ts, (F t).Nonempty)
    (hd : ∀t ∈ Ts, ∀e ∈ O t, 0 ≤ d e)
    (hmax : ∀t ∈ Ts, ∀e ∈ F t, (a e)^2 ≤ 4*c₁)
    (hmin : ∀t ∈ Ts, ∀e ∈ F t, c₂/4 ≤ d e)
    (hbad : ∀t ∈ Ts, α*((O t).card : ℝ)*(∑e ∈ O t, d e) ≤ (∑e ∈ O t, a e)^2)
    (hdom : ∀t ∈ Ts, γ*(∑e ∈ O t, a e)^2 ≤ (∑e ∈ F t, a e)^2)
    (hmult : (∑t ∈ Ts, (F t).card) ≤ 2*(Ts.biUnion F).card) :
    (α*γ/32)*(∑t ∈ Ts, ((O t).card : ℝ))*c₂ ≤ c₁*(Ts.biUnion F).card ∧
    (∑t ∈ Ts, (∑e ∈ F t, a e)^2/((O t).card : ℝ)) ≤ 8*c₁*(Ts.biUnion F).card := by
  have hcast : (∑t ∈ Ts, ((F t).card : ℝ)) ≤ 2*(Ts.biUnion F).card := by exact_mod_cast hmult
  constructor
  · have hh := sum_le_sum (fun t ht => local_density (O t) (F t) a d
      (hF t ht) (hFn t ht) hα hγ (hd t ht) (hmax t ht) (hmin t ht) (hbad t ht) (hdom t ht))
    simp only [←mul_sum,←sum_mul] at hh
    have hm := mul_le_mul_of_nonneg_left hcast (show 0 ≤ 16*c₁ by positivity)
    nlinarith
  · have hu : ∀t ∈ Ts, (∑e ∈ F t, a e)^2/((O t).card : ℝ) ≤ 4*c₁*(F t).card := by
      intro t ht
      have hm : (0:ℝ) < (O t).card := by exact_mod_cast card_pos.mpr ((hFn t ht).mono (hF t ht))
      have hfm : ((F t).card : ℝ) ≤ (O t).card := by exact_mod_cast card_le_card (hF t ht)
      have hs := sum_square_bound (F t) a (hmax t ht)
      apply (div_le_iff₀ hm).mpr
      have hh := mul_le_mul_of_nonneg_left hfm (show 0 ≤ 4*c₁*(F t).card by positivity)
      nlinarith
    have hs := sum_le_sum hu
    rw [←mul_sum] at hs
    have hh := mul_le_mul_of_nonneg_left hcast (show 0 ≤ 4*c₁ by positivity)
    nlinarith

end
end StrongThinTree.BagDensity

namespace StrongThinTree.CaptureNumeric
noncomputable section

lemma thresholds {s a ε C N N' c₁ c₂ b δ R : ℝ}
    (hs : 0 < s) (ha : s ≤ a) (ha1 : a ≤ 1)
    (he : 0 < ε) (he1 : ε ≤ 1/2) (hC : 0 < C)
    (hN : 0 < N) (hN' : 0 < N') (hNle : N' ≤ N)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (_hb : 0 < b) (hδ : 0 < δ)
    (hscale : a*N' = s*N) (hdensity : s*N*c₂ ≤ c₁*N')
    (hcard : a*N'/C ≤ b) (hcard₂ : b ≤ 2*N')
    (hmass : b*δ = a^ε*c₁*N'/C)
    (hsmall : s^ε ≤ 1/(1728*C)) (hR : R ≤ 8*c₁*N') :
    864*s^(1+2*ε)*N ≤ b ∧
    1728*s^(1+2*ε)*c₂*N ≤ δ*b ∧
    s*c₁ ≤ δ ∧ max δ (2*c₂) ≤ 2*c₁/s ∧
    s^ε*R/(6912*C) ≤ δ*b/864 := by
  have ha0 : 0 < a := hs.trans_le ha
  have hs1 : s ≤ 1 := ha.trans ha1
  have hsε : 0 < s^ε := Real.rpow_pos_of_pos hs _
  have haε : 0 < a^ε := Real.rpow_pos_of_pos ha0 _
  have hsε1 : s^ε ≤ 1 := Real.rpow_le_one hs.le hs1 he.le
  have haε1 : a^ε ≤ 1 := Real.rpow_le_one ha0.le ha1 he.le
  have hsale : s^ε ≤ a^ε := Real.rpow_le_rpow hs.le ha he.le
  have hsmall' := (le_div_iff₀ (show 0 < 1728*C by positivity)).mp hsmall
  have hη : s^(1+2*ε) = s*(s^ε)^2 := by
    rw [Real.rpow_add hs,Real.rpow_one]
    congr 1
    rw [mul_comm (2:ℝ) ε,Real.rpow_mul hs.le,Real.rpow_two]
  have hfirst : 864*s^(1+2*ε)*N ≤ b := by
    have hc := (div_le_iff₀ hC).mp hcard
    rw [hscale] at hc
    rw [hη]
    have hh : 864*(s^ε)^2*C ≤ 1 := by nlinarith only [hsmall',mul_nonneg (sub_nonneg.mpr hsε1) (by positivity : 0 ≤ 1728*C*s^ε)]
    have hmul := mul_le_mul_of_nonneg_right hh (show 0 ≤ s*N by positivity)
    apply (mul_le_mul_iff_right₀ hC).mp
    nlinarith only [hmul,hc]
  have hsecond : 1728*s^(1+2*ε)*c₂*N ≤ δ*b := by
    have hh := mul_le_mul_of_nonneg_right hdensity (show 0 ≤ 1728*(s^ε)^2*C by positivity)
    have hh' : 1728*(s^ε)^2*C ≤ a^ε := by
      have hh := mul_le_mul_of_nonneg_right hsmall' hsε.le
      nlinarith only [hh,hsale]
    have hh'' := mul_le_mul_of_nonneg_right hh' (show 0 ≤ c₁*N' by positivity)
    have hm := (eq_div_iff hC.ne').mp hmass
    rw [hη]
    apply (mul_le_mul_iff_right₀ hC).mp
    nlinarith only [hh,hh'',hm]
  have hlower : s*c₁ ≤ δ := by
    have hpow := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show ε ≤ 1-ε by linarith)
    have hex : s = s^ε*s^(1-ε) := by
      rw [←Real.rpow_add hs]
      have heq : ε+(1-ε) = 1 := by ring
      rw [heq,Real.rpow_one]
    have hh : 2*C*s ≤ s^ε := by
      have hc : 2*C*s^(1-ε) ≤ 1 := by nlinarith only [hsmall',mul_le_mul_of_nonneg_left hpow hC.le]
      have hm := mul_le_mul_of_nonneg_left hc hsε.le
      nlinarith only [hm,congrArg (fun x : ℝ => 2*C*x) hex]
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ c₁*N' by positivity)
    have hh'' := mul_le_mul_of_nonneg_right hsale (show 0 ≤ c₁*N' by positivity)
    have hm := (eq_div_iff hC.ne').mp hmass
    have hbc := mul_le_mul_of_nonneg_right hcard₂ hδ.le
    have hbcC := mul_le_mul_of_nonneg_right hbc hC.le
    apply (mul_le_mul_iff_right₀ (show 0 < 2*C*N' by positivity)).mp
    nlinarith only [hh',hh'',hm,hbcC]
  have hupperδ : δ ≤ c₁/s := by
    have hh := mul_le_mul_of_nonneg_right hcard hδ.le
    have hm := (eq_div_iff hC.ne').mp hmass
    have hc := (div_le_iff₀ hC).mp hcard
    have hhC := mul_le_mul_of_nonneg_right hh hC.le
    have hhA := mul_le_mul_of_nonneg_right haε1 (show 0 ≤ c₁*N' by positivity)
    have hhS := mul_le_mul_of_nonneg_right ha (show 0 ≤ N'*δ by positivity)
    apply (le_div_iff₀ hs).mpr
    apply (mul_le_mul_iff_right₀ hN').mp
    have hcan : (a*N'/C)*δ*C = a*N'*δ := by field_simp
    rw [hcan] at hhC
    nlinarith only [hhC,hm,hhA,hhS]
  have hupperc : c₂ ≤ c₁/s := by
    have hh := mul_le_mul_of_nonneg_left hNle (show 0 ≤ s*c₂ by positivity)
    apply (le_div_iff₀ hs).mpr
    apply (mul_le_mul_iff_right₀ hN').mp
    nlinarith only [hh,hdensity]
  refine ⟨hfirst,hsecond,hlower,max_le ?_ ?_,?_⟩
  · have hh : 0 ≤ c₁/s := by positivity
    rw [mul_div_assoc]
    linarith only [hh,hupperδ]
  · have hh := mul_le_mul_of_nonneg_left hupperc (show (0:ℝ) ≤ 2 by norm_num)
    simpa only [mul_div_assoc] using hh
  · have hh := mul_le_mul_of_nonneg_left hR hsε.le
    have hh' := mul_le_mul_of_nonneg_right hsale (show 0 ≤ 8*c₁*N' by positivity)
    have hm := (eq_div_iff hC.ne').mp hmass
    apply (div_le_iff₀ (show 0 < 6912*C by positivity)).mpr
    nlinarith only [hh,hh',hm]

end
end StrongThinTree.CaptureNumeric

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma density_spectral_input {I : Type uI} [Fintype I]
    (a d : I → ℝ) {c₁ c₂ α : ℝ}
    (hc₁ : 0 ≤ c₁) (hα : 0 ≤ α) (ha : ∀i, 0 ≤ a i)
    (hmin : ∀i, c₁ ≤ (a i)^2) (hd : ∀i, d i ≤ c₂)
    (hscale : α*c₂ ≤ c₁) :
    α*(Fintype.card I : ℝ)*(∑i, d i) ≤ (∑i, a i)^2 := by
  have hN : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hsum : (Fintype.card I : ℝ)*Real.sqrt c₁ ≤ ∑i, a i := by
    simpa only [sum_const,nsmul_eq_mul,card_univ] using
      sum_le_sum (fun i (_ : i ∈ univ) => Real.sqrt_le_iff.mpr ⟨ha i,hmin i⟩)
  have hsum0 : 0 ≤ ∑i, a i := sum_nonneg (fun i _ => ha i)
  have hsum2 : c₁*(Fintype.card I : ℝ)^2 ≤ (∑i, a i)^2 := by
    have hh := (sq_le_sq₀ (mul_nonneg hN (Real.sqrt_nonneg _)) hsum0).mpr hsum
    rw [mul_pow,Real.sq_sqrt hc₁] at hh
    nlinarith only [hh]
  have hdsum : (∑i, d i) ≤ (Fintype.card I : ℝ)*c₂ := by
    simpa only [sum_const,nsmul_eq_mul,card_univ] using sum_le_sum (fun i (_ : i ∈ univ) => hd i)
  have h1 := mul_le_mul_of_nonneg_left hdsum (mul_nonneg hα hN)
  have h2 := mul_le_mul_of_nonneg_right hscale (sq_nonneg (Fintype.card I : ℝ))
  nlinarith only [h1,h2,hsum2]

lemma homogeneous_family (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hTne : T.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ H.parentBoundary G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (he : 0 < ε) (he1 : ε < 1/3) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, c₁ ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*c₁)
    (hdmin : ∀t ∈ T, ∀e ∈ F t, c₂/4 ≤ l1dist (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, l1dist (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hbad : ∀t ∈ T, α*((H.parentBoundary G t).card : ℝ)*
      (∑e ∈ H.parentBoundary G t, l1dist (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2))) :
    let s := α*γ/32
    let R := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((H.parentBoundary G t).card : ℝ)
    (∃δ Δ : ℝ, ∃B : CompactFamily X δ Δ,
      s*c₁ ≤ δ ∧ Δ ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ δ*(∑D ∈ B.bags, (D.card : ℝ))) ∨
    (∃B : AssignedFamily H G X (s^(1+2*ε)), B.owners ⊆ T ∧
      s*c₁ ≤ B.radius ∧ B.radius ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ B.mass) := by
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => l1dist (X (G.left e)) (X (G.right e))
  let E := T.biUnion F
  let N : ℝ := ∑t ∈ T, ((H.parentBoundary G t).card : ℝ)
  let N' : ℝ := E.card
  let s := α*γ/32
  let C : ℝ := 1024/ε^2
  let R := ∑t ∈ T, (∑e ∈ F t, a e)^2/((H.parentBoundary G t).card : ℝ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hEn : E.Nonempty := by
    obtain ⟨t,ht⟩ := hTne
    obtain ⟨e,he⟩ := hFn t ht
    exact ⟨e,mem_biUnion.mpr ⟨t,ht,he⟩⟩
  have hN' : 0 < N' := by dsimp [N']; exact_mod_cast card_pos.mpr hEn
  have hboundary : ∀t ∈ T, 0 < (H.parentBoundary G t).card :=
    fun t ht => card_pos.mpr ((hFn t ht).mono (hF t ht))
  have hN : 0 < N := by
    apply sum_pos (fun t ht => ?_) hTne
    exact_mod_cast hboundary t ht
  have hNle : N' ≤ N := by
    have h1 : E.card ≤ ∑t ∈ T, (F t).card := card_biUnion_le
    have h2 : (∑t ∈ T, (F t).card) ≤ ∑t ∈ T, (H.parentBoundary G t).card :=
      sum_le_sum (fun t ht => card_le_card (hF t ht))
    dsimp [N',N]
    exact_mod_cast h1.trans h2
  have hd0 : ∀e, 0 ≤ d e := fun e => l1dist_nonneg _ _
  obtain ⟨hdensity,hR⟩ := StrongThinTree.BagDensity.family_density T (H.parentBoundary G) F a d
    hα hγ hc₁.le hF hFn (fun t ht e he => hd0 e) hmax hdmin hbad hdom
    (H.subset_boundary_multiplicity G T hT hroot F hF)
  change s*N*c₂ ≤ c₁*N' at hdensity
  change R ≤ 8*c₁*N' at hR
  let specα := s*N/N'
  have ha0 : 0 < specα := div_pos (mul_pos hs hN) hN'
  have hscale : specα*N' = s*N := div_mul_cancel₀ _ hN'.ne'
  have has : s ≤ specα := by
    apply (le_div_iff₀ hN').mpr
    exact mul_le_mul_of_nonneg_left hNle hs.le
  have had : specα*c₂ ≤ c₁ := by
    change (s*N/N')*c₂ ≤ c₁
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hN').mpr hdensity
  have hminE : ∀e ∈ E, c₁ ≤ (a e)^2 := by
    intro e he
    obtain ⟨t,ht,he⟩ := mem_biUnion.mp he
    exact hmin t ht e he
  have hmaxE : ∀e ∈ E, d e ≤ c₂ := by
    intro e he
    obtain ⟨t,ht,he⟩ := mem_biUnion.mp he
    exact hdmax t ht e he
  let u : E → Fin n := fun e => G.left e.val
  let v : E → Fin n := fun e => G.right e.val
  have hIE : Fintype.card E = E.card := Fintype.card_coe E
  have hI : 0 < Fintype.card E := by rw [hIE]; exact card_pos.mpr hEn
  have hbnd : specα*(Fintype.card E : ℝ)*(∑e : E, ‖Y (u e)-Y (v e)‖^2) ≤
      (∑e : E, (Y (u e)-Y (v e)).ofLp e.val)^2 :=
    density_spectral_input (fun e : E => a e.val) (fun e : E => ‖Y (u e)-Y (v e)‖^2)
      hc₁.le ha0.le (fun e => hpositive e.val) (fun e => hminE e.val e.property)
      (fun e => (hcontract (u e) (v e)).trans (hmaxE e.val e.property)) had
  obtain ⟨ha1,S,δ,hδ,hSE,hS2,hSc,hmass,hsep⟩ := normalized_small_balls X Y u v
    (fun e : E => e.val) Subtype.val_injective hI ha0 he he1 hc₁
    (fun e => ⟨hpositive e.val,hminE e.val e.property⟩) hbnd hcontract
  have hS : S.Nonempty := card_pos.mp (by omega)
  have hSc0 : (0:ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  have hcard : specα*N'/C ≤ (S.card : ℝ) := by
    apply (div_le_iff₀ hC).mpr
    dsimp [C]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos he)).mpr
    rw [hIE] at hSc
    change ε^2*specα*N' ≤ _ at hSc
    nlinarith only [hSc]
  have hcard₂ : (S.card : ℝ) ≤ 2*N' := by
    have hh := card_le_card hSE
    have h1 := card_union_le (univ.image u) (univ.image v)
    have h2 := card_image_le (f := u) (s := univ)
    have h3 := card_image_le (f := v) (s := univ)
    simp only [card_univ,hIE] at h2 h3
    have hSc : S.card ≤ 2*E.card := by omega
    dsimp [N']; exact_mod_cast hSc
  rw [hIE] at hmass
  change (S.card : ℝ)*δ = specα^ε*c₁*N'/C at hmass
  obtain ⟨hηδ,hηc,hlower,hupper,hgain⟩ := StrongThinTree.CaptureNumeric.thresholds
    hs has ha1 he (by linarith : ε ≤ 1/2) hC hN hN' hNle hc₁ hc₂ hSc0 hδ
    hscale hdensity hcard hcard₂ hmass hsmall hR
  let P := T.biUnion (fun t => t.filter (fun w => ∃e ∈ F t, G.left e=w ∨ G.right e=w))
  have hP : ∀w ∈ P, ∃t ∈ T, w ∈ t ∧ ∃e ∈ H.parentBoundary G t,
      (G.left e=w ∨ G.right e=w) ∧ l1dist (X (G.left e)) (X (G.right e)) ≤ c₂ := by
    intro w hw
    obtain ⟨t,ht,hw⟩ := mem_biUnion.mp hw
    obtain ⟨hwt,e,he,hew⟩ := mem_filter.mp hw
    exact ⟨t,ht,hwt,e,hF t ht he,hew,hdmax t ht e he⟩
  have hEnd : ∀e ∈ E, ∃w ∈ P, (G.left e=w ∨ G.right e=w) := by
    intro e he
    obtain ⟨t,ht,het⟩ := mem_biUnion.mp he
    have hc := (mem_filter.mp (hF t ht het)).2
    rcases hc with hc | hc
    · exact ⟨G.left e,mem_biUnion.mpr ⟨t,ht,mem_filter.mpr ⟨hc.1,e,het,Or.inl rfl⟩⟩,Or.inl rfl⟩
    · exact ⟨G.right e,mem_biUnion.mpr ⟨t,ht,mem_filter.mpr ⟨hc.1,e,het,Or.inr rfl⟩⟩,Or.inr rfl⟩
  have hcover : ∀w ∈ S, ∃p ∈ P, l1dist (X w) (X p) ≤ c₂ := by
    intro w hw
    rcases mem_union.mp (hSE hw) with hw | hw
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨p,hp,hp'⟩ := hEnd e.val e.property
      refine ⟨p,hp,?_⟩
      rcases hp' with hp' | hp'
      · simpa [u,hp',l1dist_self] using hc₂.le
      · simpa [u,d,hp'] using hmaxE e.val e.property
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨p,hp,hp'⟩ := hEnd e.val e.property
      refine ⟨p,hp,?_⟩
      rcases hp' with hp' | hp'
      · simpa [v,d,hp',l1dist_comm] using hmaxE e.val e.property
      · simpa [v,hp',l1dist_self] using hc₂.le
  have hNcast : ∑t ∈ T, ((H.parentBoundary G t).card : ℝ) = N := rfl
  have hη : 0 ≤ s^(1+2*ε) := (Real.rpow_pos_of_pos hs _).le
  obtain hcomp | hass := capture_small_balls T S P hS hT hroot hboundary hδ hc₂ hη
    hsep hcover hP hηδ hηc
  · obtain ⟨B,hB⟩ := hcomp
    refine Or.inl ⟨δ,6*max δ (2*c₂),B,hlower,?_,hgain.trans hB⟩
    change 6*max δ (2*c₂) ≤ 12*c₁/s
    calc
      _ ≤ 6*(2*c₁/s) := mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ = 12*c₁/s := by ring
  · obtain ⟨B,hBD,hBT,hB⟩ := hass
    refine Or.inr ⟨B,hBT,?_,?_,hgain.trans hB⟩
    · rw [hBD]
      exact hlower.trans (le_max_left _ _)
    · rw [hBD]
      have hh : 0 ≤ c₁/s := by positivity
      calc
        max δ (2*c₂) ≤ 2*c₁/s := hupper
        _ ≤ 12*c₁/s := by rw [mul_div_assoc,mul_div_assoc]; linarith only [hh]

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.ScaleSelection
noncomputable section
open Finset
open scoped Classical

lemma integer_dyadic {x : ℝ} (hx : 0 < x) :
    2^(⌊Real.logb 2 x⌋ : ℝ) ≤ x ∧ x < 2*2^(⌊Real.logb 2 x⌋ : ℝ) := by
  have h1 := (Real.le_logb_iff_rpow_le (by norm_num) hx).mp (Int.floor_le (Real.logb 2 x))
  have h2 := (Real.logb_lt_iff_lt_rpow (by norm_num) hx).mp (Int.lt_floor_add_one (Real.logb 2 x))
  rw [Real.rpow_add (by norm_num),Real.rpow_one] at h2
  constructor
  · exact h1
  · nlinarith only [h2]

lemma integer_dyadic_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ⌊Real.logb 2 x⌋ ≤ ⌊Real.logb 2 y⌋ :=
  Int.floor_mono (Real.logb_le_logb_of_le (by norm_num) hx hxy)

lemma integer_scale_offset {x y K : ℝ} {L : ℕ}
    (hx : 0 < x) (hxy : x ≤ y) (hK : y ≤ K*x)
    (hL : Real.logb 2 K+1 < L) :
    0 ≤ ⌊Real.logb 2 y⌋-⌊Real.logb 2 x⌋ ∧
      ⌊Real.logb 2 y⌋-⌊Real.logb 2 x⌋ < L := by
  have hy : 0 < y := hx.trans_le hxy
  have hK0 : 0 < K := by nlinarith only [hK,hy,hx]
  have hlogs : Real.logb 2 y ≤ Real.logb 2 K+Real.logb 2 x := by
    rw [←Real.logb_mul hK0.ne' hx.ne']
    exact Real.logb_le_logb_of_le (by norm_num) hy hK
  constructor
  · exact sub_nonneg.mpr (integer_dyadic_mono hx hxy)
  · have h1 := Int.floor_le (Real.logb 2 y)
    have h2 := Int.lt_floor_add_one (Real.logb 2 x)
    have hh : ((⌊Real.logb 2 y⌋-⌊Real.logb 2 x⌋ : ℤ) : ℝ) < L := by
      push_cast
      linarith only [h1,h2,hlogs,hL]
    exact_mod_cast hh

lemma select_fibers {I : Type uI2} {A : Type uA} {B : Type uB} [DecidableEq I] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Nonempty B]
    (T : Finset I) (a : I → A) (b : I → B) (w : I → ℝ) :
    ∃choice : A → B,
      (∑i ∈ T, w i)/(Fintype.card B : ℝ) ≤
        ∑i ∈ T.filter (fun i => b i = choice (a i)), w i := by
  have hB : (0:ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos (α := B)
  have hex : ∀x : A, ∃y : B,
      (∑i ∈ T.filter (fun i => a i=x), w i)/(Fintype.card B : ℝ) ≤
        ∑i ∈ (T.filter (fun i => a i=x)).filter (fun i => b i=y), w i := by
    intro x
    obtain ⟨y,hy,hgain⟩ := exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := T.filter (fun i => a i=x)) (t := univ) (f := b) (w := w)
      (fun _ _ => mem_univ _) univ_nonempty
      (b := (∑i ∈ T.filter (fun i => a i=x), w i)/(Fintype.card B : ℝ)) (by
        simp only [card_univ,nsmul_eq_mul]
        exact (mul_div_cancel₀ _ hB.ne').le)
    exact ⟨y,hgain⟩
  choose choice hchoice using hex
  refine ⟨choice,?_⟩
  have hs := sum_le_sum (s := T.image a) (fun x hx => hchoice x)
  rw [←sum_div] at hs
  have hleft : (∑x ∈ T.image a, ∑i ∈ T.filter (fun i => a i=x), w i) = ∑i ∈ T, w i := by
    exact sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem a hi) w
  rw [hleft] at hs
  have hright : (∑x ∈ T.image a, ∑i ∈ (T.filter (fun i => a i=x)).filter
      (fun i => b i=choice x), w i) = ∑i ∈ T.filter (fun i => b i=choice (a i)), w i := by
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_eq_single (a i)]
    · simp
    · intro x hx hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot (mem_image_of_mem a hi)).elim
  rw [hright] at hs
  exact hs

lemma residue_spacing {H : ℕ} (_hH : 0 < H) {n n' : ℤ}
    (hlt : n' < n) (hmod : n'%H = n%H) : n' ≤ n-H := by
  have hd : (H:ℤ) ∣ n-n' := Int.ModEq.dvd hmod
  have hh := Int.le_of_dvd (sub_pos.mpr hlt) hd
  omega

lemma separated_scales {s ρ : ℝ} {H : ℕ} {n n' : ℤ}
    (hs : 0 < s) (hρ : 0 < ρ)
    (hH : Real.logb 2 (24/(ρ*s^2)) < H)
    (hgap : n' ≤ n-H) : 24*2^(n':ℝ)/s < ρ*s*2^(n:ℝ) := by
  have hpow : 24/(ρ*s^2) < (2:ℝ)^(H:ℝ) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)).mp hH
  have hgapR : (n':ℝ)+(H:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : n'+H ≤ n)
  have hle : (2:ℝ)^(n':ℝ)*(2:ℝ)^(H:ℝ) ≤ (2:ℝ)^(n:ℝ) := by
    rw [←Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hgapR
  have hp := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (n':ℝ)
  have hh := (div_lt_iff₀ (show 0 < ρ*s^2 by positivity)).mp hpow
  have hm := mul_lt_mul_of_pos_left hh hp
  have hm' := mul_le_mul_of_nonneg_right hle (show 0 ≤ ρ*s^2 by positivity)
  apply (div_lt_iff₀ hs).mpr
  nlinarith only [hm,hm']

end
end StrongThinTree.ScaleSelection

end

end OAI
