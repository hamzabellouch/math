import OAI.NumberTheory.GaussianMoat.DyadicSieve

namespace OAI

namespace GaussianMoat

section
open scoped BigOperators Classical

structure BatchCertificate (D : ℝ) (ns : List ℕ) (N : ℕ) (s : SplitSieve)
    (L : ℕ) (E r : ℝ) where
  pre : List ℕ
  rest : List ℕ
  schedule : ns=pre++rest
  T : ℝ
  nonempty : s.primes.Nonempty
  prime_scale : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T
  large : 5≤T
  mean : 1≤ s.meanLog
  b : ℕ
  n : ℕ
  τ : ℝ
  A : ℝ
  η : ℝ
  δ : ℝ
  u : s.SignedIndex → ℝ
  band : EntropyBand s D pre 0 b δ
  coverage : CoverageDerivation s D N rest τ u η
  cap : b≤ s.primes.card
  repetitions : 0<n
  length : 0<L
  floor : 0≤τ
  gain : 0≤A
  exceptions : ∀ i, 0≤u i
  short : ∀ i, (D*L)^2<(s.signedPrime i:ℝ)
  smooth_length : L≤N
  smooth_error : ∀ i, (L:ℝ)/(N+1)≤(τ/(s.signedPrime i:ℝ))/2
  list : ∀ i, Real.log (4*u i+(s.signedPrime i:ℝ)*Real.exp
      (-(n:ℝ)*(((L:ℝ)*(τ/(s.signedPrime i:ℝ))/2)/4)))≤Real.log (s.signedPrime i)-A
  rate : (n:ℝ)*((L:ℝ)*r+2*(Real.log 36+2*Real.log (D*(rest.sum+N))))≤
      (b:ℝ)*(A*(1-2*η)-δ*s.meanLog)-E

theorem BatchCertificate.sound {D E r : ℝ} {ns : List ℕ} {N L : ℕ} {s : SplitSieve}
    (q : BatchCertificate D ns N s L E r) (hD : 1≤D)
    (z : ℕ → GaussianInt) (hz : Function.Injective z) (ha : ∀ t, z t∈s.avoiding)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (F : Finset GaussianInt) (hf : ∀ f∈F, f≠0) (hF : residueWeight F≤E) :
    ∃ G : Finset GaussianInt, F⊆G ∧ G⊆F∪s.availableFactors ∧
      r≤((TimeLaw.at 0).advance (commonSchedule z ns N)).info
        (fun a (f : G) => residueCode f.val (z a)) (incrementWord z L)
        (fun a (f : F) => residueCode f.val (z a)) / L := by
  let Q := (TimeLaw.at 0).advance (commonSchedule z q.pre 0)
  have hOld : Q.law.Hf (fun t (f : F) => residueCode f.val (z t.val))≤E :=
    (residue_finset_entropy Q.law (fun t => z t.val) F hf).trans hF
  obtain ⟨σ,π,hh⟩ := schedule_batch_information s q.nonempty z hz ha q.pre q.rest hD q.large
    q.mean hs q.prime_scale q.band q.u q.coverage (fun f : F => f.val) hOld
    q.cap q.repetitions q.length q.floor q.gain q.exceptions q.short q.smooth_length
    q.smooth_error q.list q.rate
  let f := fun j => s.signedFactorAt (s.selectedIndex q.cap σ π j)
  let G := F∪Finset.univ.image f
  refine ⟨G,Finset.subset_union_left,?_,?_⟩
  · apply Finset.union_subset Finset.subset_union_left
    intro g hg
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_union_right F (s.signed_mem_available _)
  · rw [q.schedule]
    unfold TimeLaw.info
    rw [FinLaw.cIf_finset_union]
    exact hh

theorem greedy_finite_selection (A : ℕ → Finset GaussianInt)
    (hA : ∀ j, A j⊆A (j+1)) (n : ℕ)
    (R : ℕ → Finset GaussianInt → Finset GaussianInt → Prop)
    (hstep : ∀ j≤n, ∀ F⊆A j, ∃ G, F⊆G ∧ G⊆A (j+1) ∧ R j F G) :
    ∃ F : ℕ → Finset GaussianInt,
      (∀ j, F j⊆A j) ∧ (∀ j, F j⊆F (j+1)) ∧ (∀ j≤n, R j (F j) (F (j+1))) := by
  have step (j : ℕ) (F : {F : Finset GaussianInt // F⊆A j}) :
      ∃ G : {G : Finset GaussianInt // G⊆A (j+1)}, F.val⊆G.val ∧ (j≤n → R j F.val G.val) := by
    by_cases hj : j≤n
    · obtain ⟨G,hFG,hG,hR⟩ := hstep j hj F.val F.property
      exact ⟨⟨G,hG⟩,hFG,fun _ => hR⟩
    · exact ⟨⟨F.val,F.property.trans (hA j)⟩,Finset.Subset.refl _,fun h => (hj h).elim⟩
  let f (j : ℕ) (F : {F : Finset GaussianInt // F⊆A j}) := (step j F).choose
  let F : (j : ℕ) → {F : Finset GaussianInt // F⊆A j} :=
    @Nat.rec (fun j => {F : Finset GaussianInt // F⊆A j}) ⟨∅,Finset.empty_subset _⟩ f
  refine ⟨fun j => (F j).val,fun j => (F j).property,?_,?_⟩
  · intro j
    exact (step j (F j)).choose_spec.1
  · intro j hj
    exact (step j (F j)).choose_spec.2 hj

noncomputable def precedingFactors (s : ℕ → SplitSieve) (j : ℕ) : Finset GaussianInt :=
  (Finset.range j).biUnion (fun i => (s i).availableFactors)

lemma precedingFactors_mono (s : ℕ → SplitSieve) {i j : ℕ} (h : i≤j) :
    precedingFactors s i⊆precedingFactors s j :=
by
  intro f hf
  obtain ⟨k,hk,hf⟩ := Finset.mem_biUnion.mp hf
  exact Finset.mem_biUnion.mpr ⟨k,(Finset.range_mono h) hk,hf⟩

lemma precedingFactors_succ (s : ℕ → SplitSieve) (j : ℕ) :
    precedingFactors s (j+1)=precedingFactors s j∪(s j).availableFactors := by
  simp only [precedingFactors,Finset.range_add_one,Finset.biUnion_insert,Finset.union_comm]

lemma precedingFactors_ne_zero (s : ℕ → SplitSieve) {j : ℕ} {f : GaussianInt}
    (h : f∈precedingFactors s j) : f≠0 := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
  exact (s i).available_ne_zero hi

theorem certificate_no_walk {D ε : ℝ} (hD : 1≤D) (ns : List ℕ) (N n : ℕ)
    (s : ℕ → SplitSieve) (L : ℕ → ℕ) (r : ℕ → ℝ)
    (cert : ∀ j≤n, BatchCertificate D ns N (s j) (L j)
      (residueWeight (precedingFactors s j)) (r j))
    (hdiv : ∀ j<n, L j∣L (j+1)) (hε : 0≤ε)
    (herr : ∀ j<n, ∀ a<L (j+1), 2*Real.binEntropy ((a:ℝ)/(N+1))+
      ((a:ℝ)/(N+1))*((L j:ℝ)*Real.log (latticeBall D).card+
        2*residueWeight (precedingFactors s (n+1)))≤ε)
    (hexcess : Real.log (latticeBall D).card+n*ε<∑ j∈Finset.range (n+1), r j)
    (z : ℕ → GaussianInt) (hz : Function.Injective z)
    (ha : ∀ j≤n, ∀ t, z t∈(s j).avoiding)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) : False := by
  let P := (TimeLaw.at 0).advance (commonSchedule z ns N)
  let rate (j : ℕ) (F G : Finset GaussianInt) := P.info
    (fun a (f : G) => residueCode f.val (z a)) (incrementWord z (L j))
    (fun a (f : F) => residueCode f.val (z a)) / L j
  obtain ⟨F,hFA,hFF,hR⟩ := greedy_finite_selection (precedingFactors s)
    (fun j => precedingFactors_mono s (Nat.le_succ j)) n
    (fun j F G => r j≤rate j F G) (by
      intro j hj F hF
      obtain ⟨G,hFG,hG,hI⟩ := (cert j hj).sound hD z hz (ha j hj) hs F
        (fun f hf => precedingFactors_ne_zero s (hF hf)) (residueWeight_mono hF)
      refine ⟨G,hFG,?_,hI⟩
      rw [precedingFactors_succ]
      exact hG.trans (Finset.union_subset_union_left hF))
  have ht := schedule_information_telescope z hs ns N n F hFF
    (fun j f hf => precedingFactors_ne_zero s (hFA j hf)) L
    (fun j hj => (cert j hj).length) hdiv (fun j hj => (cert j hj).smooth_length) hε (by
      intro j hj a ha
      have hw := residueWeight_mono ((hFA (j+1)).trans (precedingFactors_mono s (j := n+1) (by omega)))
      have hh := herr j hj a ha
      have hx : 0≤(a:ℝ)/(N+1) := by positivity
      change _+_ * (_+2*residueWeight (F (j+1)))≤ε
      nlinarith only [hw,hh,hx])
  have hh := Finset.sum_le_sum (s := Finset.range (n+1)) (fun j hj => hR j (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj))
  exact (not_lt_of_ge (hh.trans ht)) hexcess

open scoped BigOperators Classical
open Filter

theorem thin_bins (J : Finset ℕ) {K : ℕ} (hK : 0<K) :
    ∃ a<K, ((J.card:ℝ)/K)≤(J.filter (fun j => j%K=a)).card ∧
      ∀ i∈J.filter (fun j => j%K=a), ∀ j∈J.filter (fun j => j%K=a),
        i<j → i+K≤j := by
  have hh : (Finset.range K).card • ((J.card:ℝ)/K)≤(J.card:ℝ) := by
    rw [Finset.card_range,nsmul_eq_mul,mul_div_cancel₀ _ (by exact_mod_cast hK.ne')]
  obtain ⟨a,ha,hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := J) (t := Finset.range K) (f := fun j => j%K)
    (fun j _ => Finset.mem_range.mpr (Nat.mod_lt _ hK))
    (Finset.nonempty_range_iff.mpr hK.ne') hh
  refine ⟨a,Finset.mem_range.mp ha,hc,?_⟩
  intro i hi j hj hij
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hd : i%K=j%K := hi'.trans hj'.symm
  have hei := Nat.mod_add_div i K
  have hej := Nat.mod_add_div j K
  have hq : i/K<j/K := by nlinarith only [hei,hej,hd,hij]
  nlinarith only [hei,hej,hd,hq]

theorem eventually_separated_split_bins (K : ℕ) (hK : 0<K) :
    ∃ c δ : ℝ, 0<c ∧ 0<δ ∧ ∀ᶠ X : ℝ in atTop, ∃ J : Finset ℕ,
      c*X≤J.card ∧
      (∀ i∈J, ∀ j∈J, i<j → i+K≤j) ∧
      ∀ j∈J, X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(PrimeLogMass.dyadicBatch j).card := by
  obtain ⟨c,δ,hc,hδ,he⟩ := PrimeLogMass.eventually_dense_split_bins
  refine ⟨c/K,δ,div_pos hc (by exact_mod_cast hK),hδ,?_⟩
  filter_upwards [he] with X hX
  obtain ⟨J,hJ,hp⟩ := hX
  obtain ⟨a,_,hcard,hsep⟩ := thin_bins J hK
  refine ⟨J.filter (fun j => j%K=a),?_,hsep,?_⟩
  · have hh := (div_le_div_of_nonneg_right hJ (Nat.cast_nonneg K)).trans hcard
    simpa only [div_mul_eq_mul_div] using hh
  · intro j hj
    exact hp j (Finset.mem_filter.mp hj).1

lemma dyadicSieve_available_weight (j : ℕ) :
    residueWeight (dyadicSieve j).availableFactors≤4*Real.log 4*(2:ℝ)^j := by
  have hp : (∑ p∈PrimeLogMass.dyadicBatch j, Real.log (p:ℝ))≤Real.log 4*(2:ℝ)^(j+1) :=
    PrimeLogMass.prime_log_mass_le_theta _ (by positivity) (by
      intro p hp
      have h := (PrimeLogMass.mem_dyadicBatch j p).mp hp
      exact ⟨h.2.2.1,by exact_mod_cast h.2.1.le⟩)
  have hh := (dyadicSieve j).available_weight
  change residueWeight (dyadicSieve j).availableFactors≤2*∑ p∈PrimeLogMass.dyadicBatch j, Real.log (p:ℝ) at hh
  rw [pow_succ] at hp
  nlinarith only [hh,hp]

end

open scoped BigOperators Classical

lemma bandScale_add (g U : ℝ) (j k : ℕ) :
    bandScale g U (j+k)=bandScale g (bandScale g U j) k := by
  unfold bandScale
  rw [pow_add]
  ring

lemma bandLength_add (g U : ℝ) (j k : ℕ) :
    bandLength g U (j+k)=bandLength g (bandScale g U j) k := by
  unfold bandLength
  rw [bandScale_add]

lemma bandList_split (g U : ℝ) (j l r : ℕ) :
    List.ofFn (fun i : Fin (j+l+r) => bandLength g U i.val)=
      List.ofFn (fun i : Fin j => bandLength g U i.val)++
      List.ofFn (fun i : Fin l => bandLength g (bandScale g U j) i.val)++
      List.ofFn (fun i : Fin r => bandLength g (bandScale g U (j+l)) i.val) := by
  rw [List.ofFn_add,List.ofFn_add]
  simp only [Fin.val_castLE,Fin.val_natAdd,bandLength_add]

theorem band_first_crossing {g U V : ℝ} {m : ℕ} (hg : 0<g) (hg1 : g<1)
    (hV : 0<V) (hstart : V≤U) (hend : bandScale g U m≤V) :
    ∃ k, k ≤ m ∧ g^2*V<bandScale g U k ∧ bandScale g U k≤V := by
  have hex : ∃ k, bandScale g U k≤V := ⟨m,hend⟩
  let k := Nat.find hex
  have hk : bandScale g U k≤V := Nat.find_spec hex
  have hkm : k ≤ m := Nat.find_min' hex hend
  refine ⟨k,hkm,?_,hk⟩
  by_cases hk0 : k=0
  · simp only [hk0,bandScale,pow_zero,one_mul]
    have hg2 : g^2<1 := pow_lt_one₀ hg.le hg1 (by omega : 2≠0)
    exact (mul_lt_of_lt_one_left hV hg2).trans_le hstart
  · have hkpos : 0<k := Nat.pos_of_ne_zero hk0
    have hprev : V<bandScale g U (k-1) := lt_of_not_ge (Nat.find_min hex (by omega))
    have he : k=k-1+1 := by omega
    rw [he,bandScale_succ]
    exact mul_lt_mul_of_pos_left hprev (sq_pos_of_pos hg)

lemma bandScale_log {g U : ℝ} (hg : 0<g) (hU : 0<U) (k : ℕ) :
    Real.log (bandScale g U k)=(k:ℝ)*(2*Real.log g)+Real.log U := by
  unfold bandScale
  rw [Real.log_mul (ne_of_gt (pow_pos (sq_pos_of_pos hg) _)) hU.ne',Real.log_pow,Real.log_pow]
  norm_num

theorem schedule_log_bound (ns : List ℕ) (N : ℕ) {H : ℝ} (hH : 0≤H)
    (hns : ∀ n∈ns, (n:ℝ)≤Real.exp H) :
    Real.log ((ns.sum+N:ℕ)+1)≤Real.log ((ns.length:ℝ)+1)+H+Real.log ((N:ℝ)+1) := by
  have hs : (ns.sum:ℝ)≤(ns.length:ℝ)*Real.exp H := by
    induction ns with
    | nil => simp
    | cons n ns ih =>
      have hn := hns n (List.mem_cons_self ..)
      have hi := ih (fun m hm => hns m (List.mem_cons_of_mem n hm))
      simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith only [hn,hi]
  have he : 1≤Real.exp H := Real.one_le_exp_iff.mpr hH
  have hc : 0≤(ns.length:ℝ)*Real.exp H := mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hN : 1≤(N:ℝ)+1 := by linarith only [(Nat.cast_nonneg N : (0:ℝ)≤N)]
  have hle : ((ns.sum+N:ℕ)+1:ℝ)≤((ns.length:ℝ)+1)*Real.exp H*((N:ℝ)+1) := by
    simp only [Nat.cast_add]
    nlinarith only [hs,he,hc,hN,(Nat.cast_nonneg N : (0:ℝ)≤N)]
  have hh := Real.log_le_log (show (0:ℝ)<((ns.sum+N:ℕ)+1) by positivity) hle
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_exp] at hh
  exact hh

end GaussianMoat

end OAI
