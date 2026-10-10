import OAI.NumberTheory.GaussianMoat.WalkWords

namespace OAI

universe uIota uOmega uAlpha uGroup uGroupPrime uCapitalGamma

namespace GaussianMoat
open scoped BigOperators Classical

abbrev SplitSieve.SignedIndex (s : SplitSieve) := (Fin s.primes.card → Bool) × Fin s.primes.card

noncomputable def SplitSieve.signedPrime (s : SplitSieve) (i : s.SignedIndex) : ℕ :=
  s.enumeration i.2
noncomputable def SplitSieve.signedFactorAt (s : SplitSieve) (i : s.SignedIndex) : GaussianInt :=
  signedFactor (s.factor (s.signedPrime i)) (i.1 i.2)

lemma SplitSieve.signedFactorAt_norm (s : SplitSieve) (i : s.SignedIndex) :
    (s.signedFactorAt i).norm = (s.signedPrime i:ℤ) := by
  rw [signedFactorAt,signedFactor_norm]
  exact s.factor_norm _ (s.enumeration i.2).property

lemma SplitSieve.signedFactorAt_ne_zero (s : SplitSieve) (i : s.SignedIndex) :
    s.signedFactorAt i≠0 := by
  intro h
  have hn := s.signedFactorAt_norm i
  rw [h] at hn
  have hp := (s.prime_mem _ (s.enumeration i.2).property).ne_zero
  apply hp
  change s.signedPrime i = 0
  simpa only [Zsqrtd.norm_zero,Nat.cast_eq_zero] using hn.symm

abbrev SplitSieve.Residue (s : SplitSieve) (i : s.SignedIndex) :=
  GaussianInt ⧸ multiples (s.signedFactorAt i)
noncomputable instance SplitSieve.residueFintype (s : SplitSieve) (i : s.SignedIndex) :
    Fintype (s.Residue i) := by
  let := finite_gaussianResidue (s.signedFactorAt_ne_zero i)
  exact Fintype.ofFinite _

lemma SplitSieve.residue_card (s : SplitSieve) (i : s.SignedIndex) :
    Fintype.card (s.Residue i)=s.signedPrime i := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (GaussianInt ⧸ multiples (s.signedFactorAt i)) = _
  rw [multiples_index (s.signedFactorAt_ne_zero i),s.signedFactorAt_norm]
  simp

noncomputable def SplitSieve.residue (s : SplitSieve) (i : s.SignedIndex) :
    GaussianInt → s.Residue i := gaussianResidue (s.signedFactorAt i)

lemma SplitSieve.residue_fibers (s : SplitSieve) (i : s.SignedIndex) (z w : GaussianInt) :
    s.residue i z=s.residue i w ↔ s.residueVector i.1 z i.2=s.residueVector i.1 w i.2 := by
  change gaussianResidue _ z=gaussianResidue _ w ↔ residueCode _ z=residueCode _ w
  rw [gaussianResidue_eq,residueCode_eq]
  rfl

lemma FinLaw.uniform_expect {ι : Type uIota} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (∑ i, FinLaw.uniform ι i*f i)=𝔼 i, f i := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [FinLaw.uniform_mass,← Finset.mul_sum,div_eq_inv_mul]

lemma SplitSieve.signedIndex_nonempty (s : SplitSieve) (hne : s.primes.Nonempty) :
    Nonempty s.SignedIndex := by
  have hk := hne.card_pos
  exact ⟨(fun _ => true,⟨0,hk⟩)⟩

theorem SplitSieve.signed_coverage_deficit {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω]
    (s : SplitSieve) (hne : s.primes.Nonempty) (p : FinLaw Ω)
    (Z : Ω → GaussianInt) (C : Ω → α) (a : GaussianInt) {b : ℕ}
    (hb : 0<b) (hbk : b ≤ s.primes.card) {e E : ℝ}
    (hH : (1-e)*(b:ℝ)*s.meanLog ≤ s.pointEntropy p Z b)
    (hC : p.Hf C≤E) :
    letI := s.signedIndex_nonempty hne
    (∑ i : s.SignedIndex, FinLaw.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
      p.cHf (fun ω => s.residue i (Z ω-a)) C)) ≤ e*s.meanLog+E/b := by
  let := s.signedIndex_nonempty hne
  have hc := s.coverage_conditioning p Z C hbk
  have he (i : s.SignedIndex) :
      p.cHf (fun ω => s.residue i (Z ω-a)) C =
        p.cHf (fun ω => s.residueVector i.1 (Z ω) i.2) C := by
    apply p.cHf_congr_fibers _ _ _ _
    · intro ω ν
      change gaussianResidue _ (Z ω-a)=gaussianResidue _ (Z ν-a) ↔ _
      rw [gaussianResidue_sub,gaussianResidue_sub,sub_left_inj]
      exact s.residue_fibers i _ _
    · intro ω ν; rfl
  have hd : (∑ i : s.SignedIndex, FinLaw.uniform _ i*
      (Real.log (Fintype.card (s.Residue i))-p.cHf (fun ω => s.residue i (Z ω-a)) C)) =
      s.meanLog-(𝔼 σ : Fin s.primes.card → Bool, 𝔼 i : Fin s.primes.card,
        p.cHf (fun ω => s.residueVector σ (Z ω) i) C) := by
    rw [FinLaw.uniform_expect]
    simp only [s.residue_card,he,Finset.expect_sub_distrib]
    simp only [← Finset.univ_product_univ,Finset.expect_product]
    simp only [signedPrime,meanLog,Fintype.expect_const]
  rw [hd]
  have hbp : (0:ℝ)<b := by exact_mod_cast hb
  apply (mul_le_mul_iff_left₀ hbp).mp
  have hgoal : (s.meanLog-(𝔼 σ : Fin s.primes.card → Bool, 𝔼 i : Fin s.primes.card,
      p.cHf (fun ω => s.residueVector σ (Z ω) i) C))*(b:ℝ) ≤
        (e*s.meanLog+E/b)*(b:ℝ) := by
    rw [add_mul,div_mul_cancel₀ _ hbp.ne']
    nlinarith only [hc,hH,hC]
  exact hgoal

namespace FinLaw
variable {G : Type uGroup} [Fintype G]

noncomputable def lowResidues (p : FinLaw G) (τ : ℝ) : Finset G :=
  Finset.univ.filter (fun x => p x<τ/(Fintype.card G:ℝ))

lemma not_mem_lowResidues (p : FinLaw G) (τ : ℝ) (x : G) :
    x∉p.lowResidues τ ↔ τ/(Fintype.card G:ℝ)≤p x := by
  simp only [lowResidues,Finset.mem_filter,Finset.mem_univ,true_and,not_lt]

lemma lowResidues_prob (p : FinLaw G) (τ : ℝ) :
    p.prob (fun x => x∈p.lowResidues τ) ≤ τ*(p.lowResidues τ).card/(Fintype.card G:ℝ) := by
  have he : p.prob (fun x => x∈p.lowResidues τ)=∑ x∈p.lowResidues τ, p x := by
    unfold prob
    trans ∑ x, if x∈p.lowResidues τ then p.mass x else 0
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    · rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  rw [he]
  have hh := Finset.sum_le_sum (s := p.lowResidues τ) (fun x hx =>
    ((Finset.mem_filter.mp hx).2).le)
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  have heq : ((p.lowResidues τ).card:ℝ)*(τ/(Fintype.card G:ℝ)) =
      τ*(p.lowResidues τ).card/(Fintype.card G:ℝ) := by ring
  rw [heq] at hh
  exact hh

lemma lowResidues_equiv {G' : Type uGroupPrime} [Fintype G'] (p : FinLaw G) (e : G ≃ G') (τ : ℝ) :
    ((p.map e).lowResidues τ).card=(p.lowResidues τ).card := by
  have h : (p.map e).lowResidues τ=(p.lowResidues τ).image e := by
    ext x
    simp only [lowResidues,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_image,map_equiv_mass,Fintype.card_congr e]
    constructor
    · intro hx
      exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
    · rintro ⟨y,hy,rfl⟩
      simpa only [e.symm_apply_apply] using hy
  rw [h,Finset.card_image_of_injective _ e.injective]

theorem lowResidues_base {ι : Type uIota} [Fintype ι]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)] (w : FinLaw ι)
    (p : (i : ι) → FinLaw (G i)) (u : ι → ℝ) {τ b e : ℝ}
    (hτ : τ≤3/8) (hb : 0<b)
    (hu : ∀ i, 8*b*(Fintype.card (G i):ℝ) ≤ u i)
    (hdef : (∑ i, w i*(Real.log (Fintype.card (G i))-(p i).entropy))≤e) :
    w.prob (fun i => u i≤((p i).lowResidues τ).card) ≤ e/b := by
  apply low_mass_average G w p (fun i => (p i).lowResidues τ) _ hb
  · intro i x hx
    exact ((Finset.mem_filter.mp hx).2).le.trans
      (div_le_div_of_nonneg_right hτ (Nat.cast_nonneg _))
  · intro i hi
    have hne := (p i).nonempty
    have hp : (0:ℝ)<Fintype.card (G i) := by exact_mod_cast Fintype.card_pos
    apply (le_div_iff₀ (by positivity : (0:ℝ)<8*(Fintype.card (G i):ℝ))).mpr
    nlinarith only [hu i,hi]
  · exact hdef

theorem lowResidues_backward {Ω : Type uOmega} {Γ : Type uCapitalGamma} {ι : Type uIota} [Fintype Ω] [Fintype Γ] [Fintype ι]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)] [∀ i, AddCommGroup (G i)]
    (w : FinLaw ι) (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : (i : ι) → Ω → G i) (h : (i : ι) → Γ → G i)
    (u u' b : ι → ℝ) {τ δ ε η η' e v : ℝ} {n : ℕ}
    (hn : 0<n) (hτ : 0≤τ) (hτ1 : τ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (hε : 0≤ε) (hη : 0<η) (hu : ∀ i, 0<u i)
    (hnext : ∑ i, w i*p.prob (fun ω => u' i≤
      (((q ω).map (h i)).lowResidues (τ+4*δ)).card) ≤ η')
    (hsmall : η'+ε≤η*δ/2) (hscale : 2*(1-Real.log (η*δ/2))≤v)
    (hgap : e<η*δ*v/4)
    (hdata : (∑ i, w i*(Real.log (Fintype.card (G i))-
      (p.joint (fun ω => (q ω).iid n)).cHf (fun x => Y i x.1) Prod.snd))≤e)
    (hb : ∀ i, 1≤b i)
    (hv : ∀ i, v≤Real.log (Fintype.card (G i))-Real.log (b i))
    (hu' : ∀ i, u' i/δ≤b i)
    (herr : ∀ i, (Fintype.card (G i):ℝ)*
      Real.exp (-(n:ℝ)*δ^2*u i/(2*(Fintype.card (G i):ℝ)))≤ε) :
    w.prob (fun i => u i≤(((p.joint q).map (fun x => Y i x.1+h i x.2)).lowResidues τ).card) ≤ η := by
  let P := fun i => (p.joint q).map (fun x => Y i x.1+h i x.2)
  let K := fun i => (P i).lowResidues τ
  let B₀ := fun i => u i≤(K i).card
  let B₁ := fun i ω => u' i≤(((q ω).map (h i)).lowResidues (τ+4*δ)).card
  let E := fun i ω => (((q ω).map (h i)).lowResidues (τ+4*δ))
  apply backward_coverage_step G w p q Y h B₀ B₁ K E b hn hτ hτ1 hδ hδ1
    hε hη hnext hsmall hscale hgap hdata
  · intro i hi
    apply Finset.card_pos.mp
    have hh : (0:ℝ)<(K i).card := (hu i).trans_le hi
    exact_mod_cast hh
  · intro i _; exact hb i
  · intro i _; exact hv i
  · intro i _
    have hh := (P i).lowResidues_prob τ
    rw [prob_map] at hh
    exact hh
  · intro i _ ω _ x hx
    exact (((q ω).map (h i)).not_mem_lowResidues _ x).mp hx
  · intro i _ ω hω
    have hh : ((E i ω).card:ℝ)<u' i := lt_of_not_ge hω
    exact (div_le_div_of_nonneg_right hh.le hδ.le).trans (hu' i)
  · intro i hi
    apply le_trans _ (herr i)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hi (show 0≤(n:ℝ)*δ^2 by positivity)
    have hd := div_le_div_of_nonneg_right hh
      (show 0≤2*(Fintype.card (G i):ℝ) by positivity)
    simpa only [neg_mul,neg_div] using neg_le_neg hd

end FinLaw
end GaussianMoat

end OAI
