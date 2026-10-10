import OAI.NumberTheory.GaussianMoat.WalkPackage

namespace OAI

universe uOmega uKappa uIota uAlpha uBeta uGamma

namespace GaussianMoat
open scoped BigOperators Classical

theorem exists_batch_information {Ω : Type uOmega} {κ : Type uKappa} [Fintype Ω]
    (s : SplitSieve) (hne : s.primes.Nonempty) (p : FinLaw Ω) (a : Ω → ℕ)
    (g : κ → GaussianInt) (R : ForwardKernel) (z : ℕ → GaussianInt)
    (hz : Function.Injective z) (ha : ∀ t, z t∈s.avoiding)
    {b L N n : ℕ} (hb : b≤ s.primes.card) (hn : 0<n) (hL : 0<L)
    {D τ A η δ E r : ℝ} (hD : 1≤D) (hτ : 0≤τ) (hA : 0≤A)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (e : s.SignedIndex → ℝ) (he : ∀ i, 0≤e i)
    (hshort : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2)
    (hH : (1-δ)*(b:ℝ)*s.meanLog≤ s.pointEntropy p (fun ω => z (a ω)) b)
    (hO : p.Hf (fun ω i => residueCode (g i) (z (a ω)))≤E)
    (hBad : (𝔼 i : s.SignedIndex, p.prob (fun ω => e i≤
      (((R.then (smoothingKernel N)).relativeResidueLaw s z (a ω) i).lowResidues τ).card))≤η)
    (hnum : ∀ i, Real.log (4*e i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/4))) ≤
        Real.log (s.signedPrime i)-A)
    (hrate : (n:ℝ)*((L:ℝ)*r+2*(Real.log 36+2*Real.log (D*(R.bound+N)))) ≤
      (b:ℝ)*(A*(1-2*η)-δ*s.meanLog)-E) :
    ∃ σ : Fin s.primes.card → Bool, ∃ π : Equiv.Perm (Fin s.primes.card),
      r≤ (p.joint (fun ω => (R.then (smoothingKernel N)).law (a ω))).cIf
        (fun v j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j))
          (z (a v.1+v.2.val)))
        (fun v => incrementWord z L (a v.1+v.2.val))
        (fun v i => residueCode (g i) (z (a v.1+v.2.val))) / L := by
  let K := R.then (smoothingKernel N)
  let old := fun ω i => residueCode (g i) (z (a ω))
  let old' := FinLaw.outputCode old
  have hOld : p.Hf old'≤E := by
    apply le_trans (le_of_eq (p.Hf_eq_of_fibers old' old (fun ω ν => FinLaw.outputCode_eq_iff old ω ν))) hO
  have hD0 : 0≤D := by linarith only [hD]
  have hlower := averaged_batch_package_information s hne p a old' R z hz ha hb
    hD0 hτ hA hs e he hshort hLN herr hH hOld hBad hnum
  let Info := fun (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) =>
    (p.joint (fun ω => K.law (a ω))).cIf
      (fun v j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j)) (z (a v.1+v.2.val)))
      (fun v => incrementWord z L (a v.1+v.2.val))
      (fun v i => residueCode (g i) (z (a v.1+v.2.val)))
  have hK : 1≤K.bound := by change 1≤R.bound+N; omega
  have ht (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :
      (p.joint (fun ω => K.packageLaw z hD0 hs (a ω) L)).cIf
        (fun v j => s.residue (s.selectedIndex hb σ π j) (z (a v.1))) Prod.snd
        (fun v => old' v.1) ≤ Info σ π+2*(Real.log 36+2*Real.log (D*K.bound)) := by
    have hc := (p.joint (fun ω => K.packageLaw z hD0 hs (a ω) L)).cIf_congr_fibers
      (fun v j => s.residue (s.selectedIndex hb σ π j) (z (a v.1)))
      (fun v j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j)) (z (a v.1)))
      Prod.snd Prod.snd (fun v => old' v.1) (fun v => old v.1)
      (fun v w => by
        simp only [funext_iff,SplitSieve.residue,gaussianResidue_eq,residueCode_eq])
      (fun _ _ => Iff.rfl) (fun v w => FinLaw.outputCode_eq_iff old v.1 w.1)
    rw [hc]
    exact K.package_information_transport p a (fun j => s.signedFactorAt (s.selectedIndex hb σ π j))
      g z hD hs hK L
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => ht σ π))
  simp only [Finset.expect_add_distrib,Fintype.expect_const] at hav
  have hmul := mul_le_mul_of_nonneg_left hav (Nat.cast_nonneg n)
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hrate' : (L:ℝ)*r≤𝔼 σ, 𝔼 π, Info σ π := by
    have heK : (K.bound:ℝ)=R.bound+N := by simp only [K,ForwardKernel.then,smoothingKernel,Nat.cast_add]
    conv at hmul => rhs; rw [heK]
    have hh := hrate.trans (hlower.trans hmul)
    apply (mul_le_mul_iff_right₀ hnR).mp
    nlinarith only [hh]
  obtain ⟨σ,_,hσ⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hrate'
  obtain ⟨π,_,hπ⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hσ
  refine ⟨σ,π,?_⟩
  exact (le_div_iff₀ (show (0:ℝ)<L by exact_mod_cast hL)).mpr (by simpa only [mul_comm] using hπ)

lemma finite_entropy_telescope (n : ℕ) (a b : ℕ → ℝ) (ε : ℝ)
    (hnext : ∀ j<n, a (j+1)≤b j+ε) (hb : 0≤b n) :
    (∑ j∈Finset.range (n+1), (a j-b j)) ≤ a 0+n*ε := by
  have h : (∑ j∈Finset.range (n+1), (a j-b j)) ≤ a 0+n*ε-b n := by
    clear hb
    induction n with
    | zero => simp
    | succ n ih =>
      have hn := ih (fun j hj => hnext j (by omega))
      have hh := hnext n (by omega)
      rw [Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
      linarith only [hn,hh]
  linarith only [h,hb]

theorem word_entropy_rate_monotone {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω] [Fintype ι]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (f : ι → GaussianInt) (hf : ∀ i, f i≠0) {L K N : ℕ}
    (hL : 0<L) (hK : 0<K) (hdiv : L∣K) (hKN : K≤N) {ε : ℝ} (hε : 0≤ε)
    (herr : ∀ a<K, 2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L:ℝ)*Real.log (latticeBall D).card+
        2*∑ i, Real.log (f i).norm.natAbs) ≤ ε) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    P.cHf (fun v => incrementWord z K (t v.1+v.2.val))
      (fun v i => residueCode (f i) (z (t v.1+v.2.val))) / K ≤
    P.cHf (fun v => incrementWord z L (t v.1+v.2.val))
      (fun v i => residueCode (f i) (z (t v.1+v.2.val))) / L + ε := by
  dsimp only
  let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
  let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
  let Q := fun v i => residueCode (f i) (z (u v))
  let H := P.cHf (fun v => incrementWord z L (u v)) Q
  obtain ⟨m,hm⟩ := hdiv
  have hm' : K=m*L := by simpa [Nat.mul_comm] using hm
  have hmp : 0 < m := by nlinarith only [hK,hm]
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  have hmR : (0:ℝ) < m := by exact_mod_cast hmp
  have hblock := incrementWord_blocks_entropy P u z f L m hL
  have hsum : (∑ j : Fin m, P.cHf (fun v => incrementWord z L (u v+j.val*L))
      (fun v i => residueCode (f i) (z (u v+j.val*L)))) ≤ (m:ℝ)*(H+ε) := by
    have hh (j : Fin m) : P.cHf (fun v => incrementWord z L (u v+j.val*L))
        (fun v i => residueCode (f i) (z (u v+j.val*L))) ≤ H+ε := by
      have hj : j.val*L<K := by rw [hm']; exact Nat.mul_lt_mul_of_pos_right j.isLt hL
      have hs := word_residue_smoothing p t z hz f hf L N (j.val*L) (by omega)
      dsimp only at hs
      change P.cHf _ _ ≤ H+_+_ at hs
      have he := herr (j.val*L) hj
      linarith only [hs,he]
    have hh' := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hh j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh'
  have htotal := hblock.trans hsum
  have hd := div_le_div_of_nonneg_right htotal (show (0:ℝ)≤ m*L by positivity)
  have he : (m:ℝ)*(H+ε)/((m:ℝ)*L)=(H+ε)/L := by field_simp
  rw [he,add_div] at hd
  have hel : ε/(L:ℝ)≤ε := div_le_self hε (by exact_mod_cast hL)
  rw [hm',Nat.cast_mul]
  change P.cHf (fun v => incrementWord z (m*L) (u v)) Q / ((m:ℝ)*L) ≤ H/L+ε
  linarith only [hd,hel]

lemma FinLaw.cIf_refinement {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω]
    (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ)
    (h : ∀ ω ν, X ω = X ν → O ω = O ν) :
    p.cIf X Y O = p.cHf Y O - p.cHf Y X := by
  rw [p.cIf_comm]
  unfold FinLaw.cIf
  congr 1
  apply p.cHf_congr_fibers Y Y (fun ω => (O ω,X ω)) X
  · intro ω ν; rfl
  · intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨And.right,fun hx => ⟨h ω ν hx,hx⟩⟩

theorem common_law_information_telescope {Ω : Type uOmega} [Fintype Ω]
    (p : FinLaw Ω) (t : Ω → ℕ) (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (F : ℕ → Finset GaussianInt) (hF : ∀ j, F j ⊆ F (j+1))
    (hf : ∀ j, ∀ f ∈ F j, f ≠ 0) (L : ℕ → ℕ) (n N : ℕ)
    (hL : ∀ j ≤ n, 0 < L j) (hdiv : ∀ j < n, L j ∣ L (j+1))
    (hN : ∀ j ≤ n, L j ≤ N) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ j < n, ∀ a < L (j+1),
      2*Real.binEntropy ((a:ℝ)/(N+1)) + ((a:ℝ)/(N+1))*
        ((L j:ℝ)*Real.log (latticeBall D).card +
          2*∑ f ∈ F (j+1), Real.log f.norm.natAbs) ≤ ε) :
    let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
    let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
    (∑ j ∈ Finset.range (n+1),
      P.cIf (fun v (f : F (j+1)) => residueCode f.val (z (u v)))
        (fun v => incrementWord z (L j) (u v))
        (fun v (f : F j) => residueCode f.val (z (u v))) / L j) ≤
      Real.log (latticeBall D).card + n*ε := by
  dsimp only
  let P := p.joint (fun _ => FinLaw.uniform (Fin (N+1)))
  let u := fun v : Ω × Fin (N+1) => t v.1+v.2.val
  let Q := fun j => fun v (f : F j) => residueCode f.val (z (u v))
  let a := fun j => P.cHf (fun v => incrementWord z (L j) (u v)) (Q j) / L j
  let b := fun j => P.cHf (fun v => incrementWord z (L j) (u v)) (Q (j+1)) / L j
  have hnext (j : ℕ) (hj : j < n) : a (j+1) ≤ b j+ε := by
    dsimp only [a,b,Q,u,P]
    apply word_entropy_rate_monotone p t z hz (fun f : F (j+1) => f.val)
      (fun f => hf _ _ f.property) (hL j (by omega)) (hL (j+1) (by omega))
      (hdiv j hj) (hN (j+1) (by omega)) hε
    intro k hk
    convert herr j hj k hk using 1
    rw [Finset.sum_coe_sort (F (j+1)) (fun f : GaussianInt => Real.log f.norm.natAbs)]
  have hb : 0 ≤ b n := div_nonneg (P.cHf_nonneg _ _) (Nat.cast_nonneg _)
  have hi (j : ℕ) : P.cIf (Q (j+1)) (fun v => incrementWord z (L j) (u v)) (Q j) /
      L j = a j-b j := by
    rw [P.cIf_refinement,sub_div]
    intro v w hv
    funext f
    exact congrFun hv ⟨f.val,hF j f.property⟩
  have ht := finite_entropy_telescope n a b ε hnext hb
  have ha : a 0 ≤ Real.log (latticeBall D).card := by
    apply (div_le_iff₀ (show (0:ℝ) < L 0 by exact_mod_cast hL 0 (by omega))).mpr
    have hh := (P.cHf_le_Hf (fun v => incrementWord z (L 0) (u v)) (Q 0)).trans
      (boundedWord_entropy_le P u z hz (L 0))
    simpa only [mul_comm] using hh
  change (∑ j ∈ Finset.range (n+1), P.cIf (Q (j+1))
    (fun v => incrementWord z (L j) (u v)) (Q j) / L j) ≤ _
  simp only [hi]
  linarith only [ht,ha]

noncomputable def TimeLaw.info {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (P : TimeLaw)
    (X : ℕ → α) (Y : ℕ → β) (O : ℕ → γ) : ℝ :=
  P.law.cIf (fun t => X t.val) (fun t => Y t.val) (fun t => O t.val)

lemma TimeLaw.advance_info {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (P : TimeLaw) (K : ForwardKernel)
    (X : ℕ → α) (Y : ℕ → β) (O : ℕ → γ) :
    (P.advance K).info X Y O=(P.law.joint (fun a => K.law a.val)).cIf
      (fun v => X (v.1.val+v.2.val)) (fun v => Y (v.1.val+v.2.val))
      (fun v => O (v.1.val+v.2.val)) := by
  unfold TimeLaw.info TimeLaw.advance
  rw [FinLaw.cIf_map]
  rfl

lemma commonSchedule_smooth (z : ℕ → GaussianInt) (ns : List ℕ) (N : ℕ) :
    commonSchedule z ns N=(commonSchedule z ns 0).then (smoothingKernel N) := by
  simpa only [List.append_nil,commonSchedule,List.foldr_nil] using commonSchedule_append z ns [] N

theorem schedule_information_telescope (z : ℕ → GaussianInt) {D : ℝ}
    (hz : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (ns : List ℕ) (N n : ℕ)
    (F : ℕ → Finset GaussianInt) (hF : ∀ j, F j⊆F (j+1))
    (hf : ∀ j, ∀ f∈F j, f≠0) (L : ℕ → ℕ)
    (hL : ∀ j≤n, 0<L j) (hdiv : ∀ j<n, L j∣L (j+1)) (hN : ∀ j≤n, L j≤N)
    {ε : ℝ} (hε : 0≤ε)
    (herr : ∀ j<n, ∀ a<L (j+1), 2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L j:ℝ)*Real.log (latticeBall D).card+
        2*∑ f∈F (j+1), Real.log f.norm.natAbs)≤ε) :
    let P := (TimeLaw.at 0).advance (commonSchedule z ns N)
    (∑ j∈Finset.range (n+1), P.info
      (fun a (f : F (j+1)) => residueCode f.val (z a)) (incrementWord z (L j))
      (fun a (f : F j) => residueCode f.val (z a)) / L j)≤
        Real.log (latticeBall D).card+n*ε := by
  let Q := (TimeLaw.at 0).advance (commonSchedule z ns 0)
  have h := common_law_information_telescope Q.law (fun t => t.val) z hz F hF hf L n N
    hL hdiv hN hε herr
  dsimp only
  rw [commonSchedule_smooth,TimeLaw.advance_then]
  simp only [TimeLaw.advance_info]
  exact h

theorem schedule_batch_information (s : SplitSieve) (hne : s.primes.Nonempty)
    (z : ℕ → GaussianInt) (hz : Function.Injective z) (ha : ∀ t, z t∈s.avoiding)
    (pre rest : List ℕ) {N b L n : ℕ} {D T τ A η δ E r : ℝ}
    (hD : 1≤D) (hT : 5≤T) (hML : 1≤ s.meanLog)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (band : EntropyBand s D pre 0 b δ)
    (u : s.SignedIndex → ℝ) (coverage : CoverageDerivation s D N rest τ u η)
    {κ : Type uKappa} (f : κ → GaussianInt)
    (hOld : ((TimeLaw.at 0).advance (commonSchedule z pre 0)).law.Hf
      (fun t i => residueCode (f i) (z t.val))≤E)
    (hb : b≤ s.primes.card) (hn : 0<n) (hL : 0<L) (hτ : 0≤τ) (hA : 0≤A)
    (hu : ∀ i, 0≤u i) (hshort : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)) (hLN : L≤N)
    (herr : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2)
    (hnum : ∀ i, Real.log (4*u i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/4)))≤Real.log (s.signedPrime i)-A)
    (hrate : (n:ℝ)*((L:ℝ)*r+2*(Real.log 36+2*Real.log (D*(rest.sum+N))))≤
      (b:ℝ)*(A*(1-2*η)-δ*s.meanLog)-E) :
    ∃ σ : Fin s.primes.card → Bool, ∃ π : Equiv.Perm (Fin s.primes.card),
      r≤((TimeLaw.at 0).advance (commonSchedule z (pre++rest) N)).info
        (fun a j => residueCode (s.signedFactorAt (s.selectedIndex hb σ π j)) (z a))
        (incrementWord z L) (fun a i => residueCode (f i) (z a)) / L := by
  let P := (TimeLaw.at 0).advance (commonSchedule z pre 0)
  let R := commonSchedule z rest 0
  have hH : (1-δ)*(b:ℝ)*s.meanLog≤ s.pointEntropy P.law (fun t => z t.val) b := by
    rw [SplitSieve.pointEntropy_exact_start]
    simpa only [Nat.zero_add] using band.sound hne z hz hD hT hs hpT hML 0
  have hc := coverage.sound hne z hz hD hT hs hpT hML
  have hBad : (𝔼 i : s.SignedIndex, P.law.prob (fun ω => u i≤
      (((R.then (smoothingKernel N)).relativeResidueLaw s z ω.val i).lowResidues τ).card))≤η := by
    let := s.signedIndex_nonempty hne
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
      mul_le_mul_of_nonneg_left (hc ω.val) (P.law.nonneg ω))
    simp only [← Finset.sum_mul,P.law.sum_one,one_mul] at hh
    rw [← commonSchedule_smooth]
    unfold FinLaw.prob at hh ⊢
    rw [Finset.expect_eq_sum_div_card]
    simp only [FinLaw.uniform,Finset.mul_sum,mul_ite,mul_zero] at hh
    rw [Finset.sum_comm] at hh
    convert hh using 1
    all_goals first | rfl | simp only [Finset.card_univ,div_eq_mul_inv,Finset.sum_mul,ite_mul,zero_mul]
  obtain ⟨σ,π,hh⟩ := exists_batch_information s hne P.law (fun t => t.val) f R z hz ha
    hb hn hL hD hτ hA hs u hu hshort hLN herr hH hOld hBad hnum
    (by simpa only [R,commonSchedule_bound,Nat.add_zero] using hrate)
  refine ⟨σ,π,?_⟩
  have heR : commonSchedule z rest N=R.then (smoothingKernel N) := commonSchedule_smooth z rest N
  rw [commonSchedule_append,TimeLaw.advance_then,TimeLaw.advance_info,heR]
  exact hh

end GaussianMoat

end OAI
