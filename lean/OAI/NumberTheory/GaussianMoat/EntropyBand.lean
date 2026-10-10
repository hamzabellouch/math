import OAI.NumberTheory.GaussianMoat.SignedResidues

namespace OAI

universe uAlpha uOmega uBeta

namespace GaussianMoat
open scoped BigOperators Classical

noncomputable def ForwardKernel.displacementSymbol (K : ForwardKernel)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a : ℕ) :
    Fin (K.bound+1) → latticeBall (D*K.bound) := fun i =>
  ⟨z (a+i.val)-z a,(mem_latticeBall _ _).mpr (by
    simpa only [Nat.add_zero] using walk_pair_displacement z hD hs a K.bound i.val 0
      (by omega) (by omega))⟩

noncomputable def ForwardKernel.displacementLaw (K : ForwardKernel)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a : ℕ) :
    FinLaw (latticeBall (D*K.bound)) :=
  (K.law a).map (K.displacementSymbol z hD hs a)

lemma ForwardKernel.displacementLaw_observe (K : ForwardKernel)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a : ℕ)
    {α : Type uAlpha} [Fintype α] (f : GaussianInt → α) :
    (K.displacementLaw z hD hs a).map (fun d => f (d.val+z a))=
      (K.law a).map (fun i => f (z (a+i.val))) := by
  rw [displacementLaw,FinLaw.map_comp]
  congr 1
  funext i
  simp only [Function.comp_def,displacementSymbol,sub_add_cancel]

theorem continuation_data_entropy {Ω : Type uOmega} [Fintype Ω] (p : FinLaw Ω)
    (a : Ω → ℕ) (K : ForwardKernel) (z : ℕ → GaussianInt) {D : ℝ}
    (hD : 1≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (hK : 1≤K.bound) (n : ℕ) :
    (p.joint (fun ω => (K.displacementLaw z (by linarith only [hD]) hs (a ω)).iid n)).Hf
      Prod.snd ≤ n*(Real.log 36+2*Real.log (D*K.bound)) := by
  let q := fun ω => (K.displacementLaw z (by linarith only [hD]) hs (a ω)).iid n
  have hh := (p.joint q).Hf_le_log_card_type Prod.snd
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_pow,Real.log_pow] at hh
  have hR : 1≤D*K.bound := one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
  have hc : (0:ℝ)<(latticeBall (D*K.bound)).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0,by simpa using (show 0≤D*K.bound by positivity)⟩
  have hl := Real.log_le_log hc (latticeBall_card_le hR)
  rw [Real.log_mul (by norm_num : (36:ℝ)≠0)
    (pow_ne_zero _ (by linarith only [hR] : D*K.bound≠0)),Real.log_pow] at hl
  exact hh.trans (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _))

lemma continuation_pointEntropy {Ω : Type uOmega} [Fintype Ω] (s : SplitSieve)
    (p : FinLaw Ω) (a : Ω → ℕ) (K : ForwardKernel) (z : ℕ → GaussianInt) {D : ℝ}
    (hD : 0≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (n b : ℕ) :
    s.pointEntropy (p.joint (fun ω => (K.displacementLaw z hD hs (a ω)).iid n))
      (fun v => z (a v.1)) b = s.pointEntropy p (fun ω => z (a ω)) b := by
  let q : Ω → FinLaw (Fin n → latticeBall (D*K.bound)) := fun ω =>
    (K.displacementLaw z hD hs (a ω)).iid n
  exact s.pointEntropy_joint_fst p q (fun ω => z (a ω)) b

noncomputable def ForwardKernel.relativeResidueLaw (K : ForwardKernel)
    (s : SplitSieve) (z : ℕ → GaussianInt) (a : ℕ) (i : s.SignedIndex) : FinLaw (s.Residue i) :=
  (K.law a).map (fun t => s.residue i (z (a+t.val)-z a))

lemma ForwardKernel.displacementLaw_residue (K : ForwardKernel)
    (s : SplitSieve) (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a : ℕ) (i : s.SignedIndex) :
    (K.displacementLaw z hD hs a).map (fun d => s.residue i d.val)=
      K.relativeResidueLaw s z a i := by
  rw [ForwardKernel.displacementLaw,FinLaw.map_comp]
  rfl

lemma ForwardKernel.then_relativeResidueLaw (K R : ForwardKernel)
    (s : SplitSieve) (z : ℕ → GaussianInt) {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (a : ℕ) (i : s.SignedIndex) :
    (K.then R).relativeResidueLaw s z a i =
      ((K.law a).joint (fun t => R.displacementLaw z hD hs (a+t.val))).map
        (fun v => s.residue i (z (a+v.1.val)-z a)+s.residue i v.2.val) := by
  unfold relativeResidueLaw ForwardKernel.then
  rw [FinLaw.map_comp,FinLaw.joint_observation_fun,FinLaw.joint_observation_fun]
  congr 1
  funext t
  rw [ForwardKernel.displacementLaw,FinLaw.map_comp]
  congr 1
  funext u
  change s.residue i (z (a+(t.val+u.val))-z a) =
    s.residue i (z (a+t.val)-z a)+s.residue i (z (a+t.val+u.val)-z (a+t.val))
  unfold SplitSieve.residue
  rw [← gaussianResidue_add]
  congr 1
  rw [Nat.add_assoc]
  abel

lemma FinLaw.cHf_const_right {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω]
    (p : FinLaw Ω) (X : Ω → α) (c : β) : p.cHf X (fun _ => c)=p.Hf X := by
  unfold cHf
  rw [p.Hf_const,sub_zero]
  apply p.Hf_eq_of_fibers
  intro ω ν
  simp only [Prod.mk.injEq,and_true]

lemma ForwardKernel.residue_deficit (K : ForwardKernel)
    (s : SplitSieve) (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) (a : ℕ)
    {b : ℕ} (hb : 0<b) (hbk : b≤ s.primes.card) {e : ℝ}
    (hH : (1-e)*(b:ℝ)*s.meanLog≤ s.pointEntropy (K.law a) (fun t => z (a+t.val)) b) :
    letI := s.signedIndex_nonempty hne
    (∑ i : s.SignedIndex, FinLaw.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
      (K.relativeResidueLaw s z a i).entropy))≤e*s.meanLog := by
  let := s.signedIndex_nonempty hne
  have hh := s.signed_coverage_deficit hne (K.law a) (fun t => z (a+t.val))
    (fun _ => ()) (z a) hb hbk hH (E := 0) (by rw [FinLaw.Hf_const])
  simp only [FinLaw.cHf_const_right,zero_div,add_zero] at hh
  change (∑ i, FinLaw.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
    (K.law a).H (fun t => s.residue i (z (a+t.val)-z a))))≤_
  simpa only [FinLaw.Hf_eq_H] using hh

theorem ForwardKernel.coverage_base (K : ForwardKernel)
    (s : SplitSieve) (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) (a : ℕ)
    {b : ℕ} (hb : 0<b) (hbk : b≤ s.primes.card) {e τ c : ℝ} (u : s.SignedIndex → ℝ)
    (hτ : τ≤3/8) (hc : 0<c) (hu : ∀ i, 8*c*(s.signedPrime i:ℝ)≤u i)
    (hH : (1-e)*(b:ℝ)*s.meanLog≤ s.pointEntropy (K.law a) (fun t => z (a+t.val)) b) :
    letI := s.signedIndex_nonempty hne
    (FinLaw.uniform s.SignedIndex).prob (fun i =>
      u i≤((K.relativeResidueLaw s z a i).lowResidues τ).card) ≤e*s.meanLog/c := by
  let := s.signedIndex_nonempty hne
  apply FinLaw.lowResidues_base s.Residue (FinLaw.uniform _) (K.relativeResidueLaw s z a) u
    hτ hc
  · intro i
    simpa only [s.residue_card] using hu i
  · exact K.residue_deficit s hne z a hb hbk hH

lemma ForwardKernel.coverage_data_deficit (K R : ForwardKernel)
    (s : SplitSieve) (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) {D : ℝ}
    (hD : 1≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (hR : 1≤R.bound)
    (a n : ℕ) {b : ℕ} (hb : 0<b) (hbk : b≤ s.primes.card) {e : ℝ}
    (hH : (1-e)*(b:ℝ)*s.meanLog≤ s.pointEntropy (K.law a) (fun t => z (a+t.val)) b) :
    letI := s.signedIndex_nonempty hne
    (∑ i : s.SignedIndex, FinLaw.uniform _ i*(Real.log (Fintype.card (s.Residue i))-
      ((K.law a).joint (fun t => (R.displacementLaw z (by linarith only [hD]) hs (a+t.val)).iid n)).cHf
        (fun v => s.residue i (z (a+v.1.val)-z a)) Prod.snd)) ≤
      e*s.meanLog+n*(Real.log 36+2*Real.log (D*R.bound))/b := by
  let := s.signedIndex_nonempty hne
  let q := fun t : Fin (K.bound+1) =>
    (R.displacementLaw z (by linarith only [hD]) hs (a+t.val)).iid n
  let P := (K.law a).joint q
  have he : s.pointEntropy P (fun v => z (a+v.1.val)) b =
      s.pointEntropy (K.law a) (fun t => z (a+t.val)) b :=
    s.pointEntropy_joint_fst (K.law a) q (fun t => z (a+t.val)) b
  have hH' : (1-e)*(b:ℝ)*s.meanLog≤ s.pointEntropy P (fun v => z (a+v.1.val)) b := by
    rw [he]; exact hH
  exact s.signed_coverage_deficit hne P (fun v => z (a+v.1.val)) Prod.snd (z a)
    hb hbk hH' (continuation_data_entropy (K.law a) (fun t => a+t.val) R z hD hs hR n)

theorem ForwardKernel.coverage_backward (K R : ForwardKernel)
    (s : SplitSieve) (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) {D : ℝ}
    (hD : 1≤D) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (hR : 1≤R.bound)
    (a : ℕ) (u u' c : s.SignedIndex → ℝ) {τ δ ε η η' e v : ℝ} {n b : ℕ}
    (hn : 0<n) (hb : 0<b) (hbk : b≤ s.primes.card)
    (hτ : 0≤τ) (hτ1 : τ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (hε : 0≤ε) (hη : 0<η) (hu : ∀ i, 0<u i)
    (hH : (1-e)*(b:ℝ)*s.meanLog≤ s.pointEntropy (K.law a) (fun t => z (a+t.val)) b)
    (hnext : ∀ t, letI := s.signedIndex_nonempty hne
      (FinLaw.uniform s.SignedIndex).prob (fun i => u' i≤
        ((R.relativeResidueLaw s z t i).lowResidues (τ+4*δ)).card)≤η')
    (hsmall : η'+ε≤η*δ/2) (hscale : 2*(1-Real.log (η*δ/2))≤v)
    (hgap : e*s.meanLog+n*(Real.log 36+2*Real.log (D*R.bound))/b<η*δ*v/4)
    (hc : ∀ i, 1≤c i) (hv : ∀ i, v≤Real.log (s.signedPrime i)-Real.log (c i))
    (hu' : ∀ i, u' i/δ≤c i)
    (herr : ∀ i, (s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*δ^2*u i/(2*(s.signedPrime i:ℝ)))≤ε) :
    letI := s.signedIndex_nonempty hne
    (FinLaw.uniform s.SignedIndex).prob (fun i =>
      u i≤(((K.then R).relativeResidueLaw s z a i).lowResidues τ).card)≤η := by
  let := s.signedIndex_nonempty hne
  let w := FinLaw.uniform s.SignedIndex
  let q := fun t : Fin (K.bound+1) => R.displacementLaw z (by linarith only [hD]) hs (a+t.val)
  have hnxt : (∑ i, w i*(K.law a).prob (fun t => u' i≤
      (((q t).map (fun d => s.residue i d.val)).lowResidues (τ+4*δ)).card))≤η' := by
    simp only [q,ForwardKernel.displacementLaw_residue,FinLaw.prob,Finset.mul_sum]
    rw [Finset.sum_comm]
    have he : (∑ t, ∑ i, w i*(if u' i≤
        ((R.relativeResidueLaw s z (a+t.val) i).lowResidues (τ+4*δ)).card then K.law a t else 0)) =
        ∑ t, K.law a t*w.prob (fun i => u' i≤
          ((R.relativeResidueLaw s z (a+t.val) i).lowResidues (τ+4*δ)).card) := by
      unfold FinLaw.prob
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    rw [he]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ =>
      mul_le_mul_of_nonneg_left (hnext (a+t.val)) ((K.law a).nonneg t))
    simpa only [← Finset.sum_mul,(K.law a).sum_one,one_mul] using hh
  have hd := K.coverage_data_deficit R s hne z hD hs hR a n hb hbk hH
  have hh := FinLaw.lowResidues_backward s.Residue w (K.law a) q
    (fun i t => s.residue i (z (a+t.val)-z a)) (fun i d => s.residue i d.val)
    u u' c hn hτ hτ1 hδ hδ1 hε hη hu hnxt hsmall hscale hgap hd hc
    (by intro i; simpa only [s.residue_card] using hv i) hu'
    (by intro i; simpa only [s.residue_card] using herr i)
  have he (i : s.SignedIndex) := K.then_relativeResidueLaw R s z
    (by linarith only [hD]) hs a i
  simpa only [he] using hh

structure EntropyBand (s : SplitSieve) (D : ℝ) (ns : List ℕ) (N b : ℕ) (δ : ℝ) where
  pre : List ℕ
  post : List ℕ
  g : ℝ
  U : ℝ
  l : ℕ
  e : ℝ
  schedule : ns=pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post
  size : b=bandSize s g U l
  positive : 0<g
  small : g≤1/200
  scale : 0<U
  logarithmic : 2*(1+Real.log 18)≤g*bandScale g U l
  large : 640*s.meanLog≤g^5*bandScale g U l
  alphabet : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ))≤g^2*bandScale g U l
  displacement : 4*Real.log D+2*Real.log 36≤4*g*bandScale g U l
  geometry : 2*Real.log 16+4*Real.log D≤bandScale g U l/4
  cap : ⌊U/s.meanLog⌋₊≤ s.primes.card
  cost : Real.log 36+2*Real.log (D*((post.sum+N:ℕ)+1))≤e*(bandSize s g U l:ℝ)*s.meanLog
  deficit : (1/2:ℝ)^l+80*g+e≤δ

theorem EntropyBand.sound {s : SplitSieve} {D T : ℝ} {ns : List ℕ} {N b : ℕ} {δ : ℝ}
    (q : EntropyBand s D ns N b δ) (hne : s.primes.Nonempty)
    (z : ℕ → GaussianInt) (hz : Function.Injective z) (hD : 1≤D) (hT : 5≤T)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T) (hL : 1≤ s.meanLog) (a : ℕ) :
    (1-δ)*(b:ℝ)*s.meanLog≤
      s.pointEntropy ((commonSchedule z ns N).law a) (fun t => z (a+t.val)) b := by
  rcases q with ⟨pre,post,g,U,l,e,heq,hb,hg,hg1,hU,hlog,hlarge,hsize,hdisp,hgeom,hcap,hcost,hδ⟩
  subst ns b
  have hh := commonSchedule_subband_entropy s hne z hz pre post a N hD hT hs hpT
    hg hg1 hL hU hlog hlarge hsize hdisp hgeom hcap hcost
  have hn : 0≤(bandSize s g U l:ℝ)*s.meanLog := mul_nonneg (Nat.cast_nonneg _) (by linarith only [hL])
  nlinarith only [hh,hδ,hn]

inductive CoverageDerivation (s : SplitSieve) (D : ℝ) (N : ℕ) :
    List ℕ → ℝ → (s.SignedIndex → ℝ) → ℝ → Prop
  | base (ns : List ℕ) (b : ℕ) (τ c e η : ℝ) (u : s.SignedIndex → ℝ)
      (band : EntropyBand s D ns N b e)
      (hb : 0<b) (hbk : b≤ s.primes.card) (hτ : τ≤3/8) (hc : 0<c)
      (hu : ∀ i, 8*c*(s.signedPrime i:ℝ)≤u i) (hη : e*s.meanLog/c≤η) :
      CoverageDerivation s D N ns τ u η
  | step (ns rest : List ℕ) (b n : ℕ) (τ δ ε η η' e v : ℝ)
      (u u' c : s.SignedIndex → ℝ)
      (band : EntropyBand s D ns 0 b e)
      (next : CoverageDerivation s D N rest (τ+4*δ) u' η')
      (hR : 1≤rest.sum+N) (hn : 0<n) (hb : 0<b) (hbk : b≤ s.primes.card)
      (hτ : 0≤τ) (hτ1 : τ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
      (hε : 0≤ε) (hη : 0<η) (hu : ∀ i, 0<u i)
      (hsmall : η'+ε≤η*δ/2) (hscale : 2*(1-Real.log (η*δ/2))≤v)
      (hgap : e*s.meanLog+n*(Real.log 36+2*Real.log (D*(rest.sum+N)))/b<η*δ*v/4)
      (hc : ∀ i, 1≤c i) (hv : ∀ i, v≤Real.log (s.signedPrime i)-Real.log (c i))
      (hu' : ∀ i, u' i/δ≤c i)
      (herr : ∀ i, (s.signedPrime i:ℝ)*Real.exp
        (-(n:ℝ)*δ^2*u i/(2*(s.signedPrime i:ℝ)))≤ε) :
      CoverageDerivation s D N (ns++rest) τ u η

theorem CoverageDerivation.sound {s : SplitSieve} {D T : ℝ} {N : ℕ}
    {ns : List ℕ} {τ η : ℝ} {u : s.SignedIndex → ℝ}
    (q : CoverageDerivation s D N ns τ u η) (hne : s.primes.Nonempty)
    (z : ℕ → GaussianInt) (hz : Function.Injective z) (hD : 1≤D) (hT : 5≤T)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T) (hL : 1≤ s.meanLog) :
    ∀ a, letI := s.signedIndex_nonempty hne
      (FinLaw.uniform s.SignedIndex).prob (fun i => u i≤
        (((commonSchedule z ns N).relativeResidueLaw s z a i).lowResidues τ).card)≤η := by
  let := s.signedIndex_nonempty hne
  induction q with
  | base ns b τ c e η u band hb hbk hτ hc hu hη =>
    intro a
    exact ((commonSchedule z ns N).coverage_base s hne z a hb hbk u hτ hc hu
      (band.sound hne z hz hD hT hs hpT hL a)).trans hη
  | step ns rest b n τ δ ε η η' e v u u' c band next hR hn hb hbk hτ hτ1 hδ hδ1
      hε hη hu hsmall hscale hgap hc hv hu' herr ih =>
    intro a
    rw [commonSchedule_append]
    apply (commonSchedule z ns 0).coverage_backward (commonSchedule z rest N) s hne z
      hD hs (by simpa only [commonSchedule_bound] using hR) a u u' c hn hb hbk hτ hτ1 hδ hδ1 hε hη hu
      (band.sound hne z hz hD hT hs hpT hL a) ih hsmall hscale
    · simpa only [commonSchedule_bound,Nat.cast_add] using hgap
    · exact hc
    · exact hv
    · exact hu'
    · exact herr

end GaussianMoat

end OAI
