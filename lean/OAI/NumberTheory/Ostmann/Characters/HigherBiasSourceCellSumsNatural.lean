import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellSumsCover
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellSumsTargets

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource

theorem exists_natural_cell_target_lists (c : ℝ) (hc : 0<c) :
    ∃ N : ℕ, 0<N ∧ ∀ (b T : ℝ) (I : Finset ℕ),
      1≤b → 2≤c*b → (∀ x∈I,b≤(x:ℝ) ∧ (x:ℝ)≤3*b) → c*b≤(I.card:ℝ) →
      (N:ℝ)≤T/b →
      ∃ l : List ℕ, (∀ x∈l,x∈I) ∧ |(l.sum:ℝ)-T|≤6/c ∧
        T/(6*b)≤(l.length:ℝ) ∧ (l.length:ℝ)≤2*T/b := by
  obtain ⟨R,hR⟩ := exists_uniform_cell_residue_cover c hc
  obtain ⟨N,hN,hTarget⟩ := exists_target_interior_rounding (c/2) (by positivity) R
  refine ⟨N,hN,?_⟩
  intro b T I hb hlarge hband hcard hT
  have hb0 : 0<b := lt_of_lt_of_le zero_lt_one hb
  have hI : 1<I.card := by
    have hh : (2:ℝ)≤I.card := hlarge.trans hcard
    exact_mod_cast (show (1:ℝ)<I.card by linarith)
  obtain ⟨C⟩ := exists_normalizedCellSet I hI
  have hbase := (hband C.base C.base_mem).1
  have hmax := (hband (C.base+C.gcd*C.endpoint) C.max_mem).2
  have hm := C.real_margins hb0 hc hlarge hcard hbase hmax
  obtain ⟨r,hr,hcover⟩ := hR C hb0 hlarge hcard hbase hmax
  have hmax' : (C.base:ℝ)+(C.gcd:ℝ)*C.endpoint≤3*b := by exact_mod_cast hmax
  obtain ⟨n,t,hn,htlo,hthi,herr,hnlo,hnhi⟩ :=
    hTarget b T C.base C.gcd C.endpoint r hb C.gcd_pos C.endpoint_pos hr hbase hmax' hm.1 hT
  obtain ⟨l,hlen,hmem,hsum⟩ := C.lift_list hn htlo hthi hcover
  refine ⟨l,hmem,?_,by simpa only [hlen] using hnlo,by simpa only [hlen] using hnhi⟩
  have herr' : |((l.sum:ℕ):ℝ)-T|≤(C.gcd:ℝ) := by simpa only [hsum] using herr
  exact herr'.trans hm.2.1

end Ostmann.Characters.HigherBiasSource

end

end OAI
