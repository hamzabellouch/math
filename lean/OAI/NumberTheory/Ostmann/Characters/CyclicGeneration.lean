import OAI.NumberTheory.Ostmann.Characters.DenseAdditiveCoverage

namespace OAI

noncomputable section
open scoped BigOperators Pointwise
namespace Ostmann.Characters

theorem closure_cast_eq_top_of_gcd_one (I : Finset ℤ) (hgcd : I.gcd id=1) (s : ℕ) :
    AddSubgroup.closure (I.image (fun x:ℤ => (x:ZMod s)) : Set (ZMod s)) = ⊤ := by
  classical
  let K := AddSubgroup.closure (I.image (fun x:ℤ => (x:ZMod s)) : Set (ZMod s))
  have hi (x:ℤ) (hx:x∈I) : (x:ZMod s)∈K :=
    AddSubgroup.subset_closure (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  obtain ⟨c,hc⟩ := I.gcd_eq_sum_mul id
  rw [hgcd] at hc
  have hsum : (∑ x∈I,(c x) • (x:ZMod s))∈K := K.sum_mem (fun x hx => K.zsmul_mem (hi x hx) _)
  have hone : (1:ZMod s)∈K := by
    have hz := congrArg (fun x:ℤ => (x:ZMod s)) hc
    simp only [Int.cast_one, Int.cast_sum, Int.cast_mul, id_eq] at hz
    convert hsum using 1
    rw [hz]
    apply Finset.sum_congr rfl
    intro x hx
    rw [zsmul_eq_mul, mul_comm]
  apply top_unique
  intro z hz
  obtain ⟨n,rfl⟩ := ZMod.intCast_surjective z
  simpa only [zsmul_eq_mul, mul_one] using K.zsmul_mem hone n

theorem integer_residue_cover (I : Finset ℤ) (h0 : 0∈I) (hgcd : I.gcd id=1)
    {s : ℕ} [NeZero s] (N : ℕ)
    (hsize : (s:ℚ) < (3/2:ℚ)^N*(I.image (fun x:ℤ => (x:ZMod s))).card) :
    ∃ r≤2^N, ∀z:ZMod s, ∃ f:Fin r→ℤ,
      (∀i,f i∈I) ∧ ∑i,(f i:ZMod s)=z := by
  classical
  let A := I.image (fun x:ℤ => (x:ZMod s))
  have ha0 : (0:ZMod s)∈A := Finset.mem_image.mpr ⟨0,h0,Int.cast_zero⟩
  obtain ⟨r,hr,hcover⟩ := exists_ordered_sum_cover A ha0
    (closure_cast_eq_top_of_gcd_one I hgcd s) N (by simpa only [ZMod.card] using hsize)
  refine ⟨r,hr,?_⟩
  intro z
  obtain ⟨f,hf,hfsum⟩ := hcover z
  have hpre : ∀i:Fin r,∃x:ℤ,x∈I ∧ (x:ZMod s)=f i := fun i => Finset.mem_image.mp (hf i)
  choose g hg hgf using hpre
  refine ⟨g,hg,?_⟩
  simpa only [hgf] using hfsum
end Ostmann.Characters

end

end OAI
