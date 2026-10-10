import OAI.NumberTheory.GaussianMoat.BatchCertificate

namespace OAI

namespace GaussianMoat
open scoped BigOperators Classical

structure SieveCertificate (D : ℝ) where
  schedule : List ℕ
  smoothing : ℕ
  batches : ℕ → ℕ
  last : ℕ
  lengths : ℕ → ℕ
  rates : ℕ → ℝ
  error : ℝ
  batch : ∀ j≤last, BatchCertificate D schedule smoothing (dyadicSieve (batches j)) (lengths j)
    (residueWeight (precedingFactors (fun i => dyadicSieve (batches i)) j)) (rates j)
  divides : ∀ j<last, lengths j∣lengths (j+1)
  nonneg : 0≤error
  smooth : ∀ j<last, ∀ a<lengths (j+1), 2*Real.binEntropy ((a:ℝ)/(smoothing+1))+
    ((a:ℝ)/(smoothing+1))*((lengths j:ℝ)*Real.log (latticeBall D).card+
      2*residueWeight (precedingFactors (fun i => dyadicSieve (batches i)) (last+1)))≤error
  excess : Real.log (latticeBall D).card+last*error<∑ j∈Finset.range (last+1), rates j

noncomputable def SieveCertificate.primes {D : ℝ} (q : SieveCertificate D) : Finset ℕ :=
  (Finset.range (q.last+1)).biUnion (fun j => PrimeLogMass.dyadicBatch (q.batches j))

lemma SieveCertificate.primes_spec {D : ℝ} (q : SieveCertificate D) :
    ∀ p∈q.primes, p.Prime ∧ p%4=1 := by
  intro p hp
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
  exact (PrimeLogMass.mem_dyadicBatch _ _ |>.mp hj).2.2

noncomputable def SieveCertificate.sieve {D : ℝ} (q : SieveCertificate D) : SplitSieve :=
  splitSieveOf q.primes q.primes_spec

lemma SieveCertificate.avoiding_batch {D : ℝ} (q : SieveCertificate D)
    {z : GaussianInt} (hz : z∈q.sieve.avoiding) {j : ℕ} (hj : j≤q.last) :
    z∈(dyadicSieve (q.batches j)).avoiding := by
  intro p hp
  exact hz p (Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr (by omega),hp⟩)

theorem SieveCertificate.sound {D : ℝ} (q : SieveCertificate D) (hD : 1≤D) :
    ∀ z : ℕ → GaussianInt, (∀ t, z t∈q.sieve.avoiding) → Function.Injective z →
      (∀ t, dist (z (t+1):ℂ) (z t:ℂ)≤D) → False := by
  intro z ha hz hs
  exact certificate_no_walk hD q.schedule q.smoothing q.last
    (fun j => dyadicSieve (q.batches j)) q.lengths q.rates q.batch q.divides
    q.nonneg q.smooth q.excess z hz (fun _ hj t => q.avoiding_batch (ha t) hj)
    (fun t => by simpa only [dist_comm] using hs t)

theorem finiteSieve_of_certificates
    (h : ∀ D : ℝ, 1≤D → Nonempty (SieveCertificate D)) : FiniteSieveEndpoint := by
  intro D hD
  obtain ⟨q⟩ := h D hD
  exact ⟨q.sieve,q.sound hD⟩

theorem entropyBand_from_suffix (s : SplitSieve) (pre post : List ℕ) (N l : ℕ)
    {D g U δ : ℝ} (hD : 1≤D) (hg : 0<g) (hg1 : g≤1/200) (hU : 0<U)
    (hL : 1≤ s.meanLog)
    (hlog : 2*(1+Real.log 18)≤g*bandScale g U l)
    (hlarge : 640*s.meanLog≤g^5*bandScale g U l)
    (hsize : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ))≤g^2*bandScale g U l)
    (hdisp : 4*Real.log D+2*Real.log 36≤4*g*bandScale g U l)
    (hgeom : 2*Real.log 16+4*Real.log D≤bandScale g U l/4)
    (hcap : ⌊U/s.meanLog⌋₊≤ s.primes.card)
    (hpost : ∀ n∈post, (n:ℝ)≤Real.exp (g*bandScale g U l))
    (hN : (N:ℝ)≤Real.exp (g*bandScale g U l))
    (hlen : (post.length+2:ℝ)≤Real.exp (g*bandScale g U l))
    (hconst : Real.log 36+2*Real.log D≤g*bandScale g U l)
    (hδ : (1/2:ℝ)^l+90*g≤δ) :
    Nonempty (EntropyBand s D
      (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post)
      N (bandSize s g U l) δ) := by
  let V := bandScale g U l
  have hV : 0<V := bandScale_pos hg hU l
  have hLp : 0<s.meanLog := by linarith only [hL]
  have hg5 : g^5≤1 := pow_le_one₀ hg.le (by linarith only [hg1])
  have hVL : 2*s.meanLog≤V := by
    have hh := mul_le_mul_of_nonneg_right hg5 hV.le
    change 640*s.meanLog≤g^5*V at hlarge
    nlinarith only [hlarge,hh,hLp]
  have hfloor : V/2≤(bandSize s g U l:ℝ)*s.meanLog := by
    have hh := Nat.lt_floor_add_one (V/s.meanLog)
    have hm := mul_lt_mul_of_pos_right hh hLp
    rw [div_mul_cancel₀ _ hLp.ne',add_mul,one_mul] at hm
    change V/2≤(⌊V/s.meanLog⌋₊:ℝ)*s.meanLog
    linarith only [hm,hVL]
  have hshift := commonSchedule_log_bound (fun _ => (0:GaussianInt)) post N hpost hN hlen
  simp only [commonSchedule_bound,Nat.cast_add] at hshift
  rw [show 1+((post.sum:ℝ)+N)=(post.sum:ℝ)+N+1 by ring] at hshift
  have hcost : Real.log 36+2*Real.log (D*((post.sum+N:ℕ)+1))≤
      (10*g)*(bandSize s g U l:ℝ)*s.meanLog := by
    rw [Real.log_mul (by linarith only [hD] : D≠0) (by positivity)]
    simp only [Nat.cast_add]
    have hc : Real.log 36+2*Real.log D≤g*V := hconst
    have hm := mul_le_mul_of_nonneg_left hfloor (show 0≤10*g by positivity)
    nlinarith only [hshift,hc,hm]
  exact ⟨⟨pre,post,g,U,l,10*g,rfl,rfl,hg,hg1,hU,hlog,hlarge,hsize,hdisp,hgeom,
    hcap,hcost,by linarith only [hδ]⟩⟩

lemma bandLength_le_exp_start {g U : ℝ} (hg : 0≤g) (hg1 : g≤1) (hU : 0≤U) (j : ℕ) :
    (bandLength g U j:ℝ)≤Real.exp (g*U) := by
  apply (Nat.floor_le (Real.exp_nonneg _)).trans
  apply Real.exp_le_exp.mpr
  have hh := bandScale_antitone hg hg1 hU (Nat.zero_le j)
  simpa only [bandScale,pow_zero,one_mul] using mul_le_mul_of_nonneg_left hh hg

lemma bandLength_le_exp_at {g U : ℝ} (hg : 0≤g) (hg1 : g≤1) (hU : 0≤U)
    {i j : ℕ} (hij : i≤j) :
    (bandLength g U j:ℝ)≤Real.exp (g*bandScale g U i) := by
  exact (Nat.floor_le (Real.exp_nonneg _)).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (bandScale_antitone hg hg1 hU hij) hg))

end GaussianMoat

end OAI
