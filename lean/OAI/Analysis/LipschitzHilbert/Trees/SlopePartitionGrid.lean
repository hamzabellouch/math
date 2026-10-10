import OAI.Analysis.LipschitzHilbert.Estimates.SlopePartition
import OAI.Analysis.LipschitzHilbert.Phase.AngularNormalization

namespace OAI

/-! The exact finite smooth partition uses the same arithmetic labels as
the packet model; their local multiplicity is uniform in the truncation. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceSlopeLabels

theorem injective_integer_multiplicity {ι : Type*} [Fintype ι]
    (index : ι → ℤ) (hinj : Function.Injective index)
    (offset spacing precision : ℝ) (hs : 0<spacing) (hp : 0≤precision)
    (K : ℕ) (hK : precision≤2*K*spacing) :
    LocalMultiplicity Finset.univ (fun i => offset+spacing*(index i:ℝ)) precision (2*K+1) := by
  classical
  have h := integer_slope_multiplicity (Finset.univ.image index) offset spacing precision hs hp K hK
  intro a
  apply (Finset.card_le_card_of_injOn index ?_ (fun _ _ _ _ heq => hinj heq)).trans (h a)
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,(Finset.mem_filter.mp hi).2⟩

end LipschitzHilbert.SourceSlopeLabels
namespace LipschitzHilbert.PacketRepresentation

def finiteSlopeLabels (K : ℕ) : Finset ℕ := Finset.range (2*K+1)
def finiteSlopeCenter (K : ℕ) (delta d : ℝ) (n : ℕ) : ℝ := delta*d*((n:ℝ)-K)

def scaledSlopePartition (delta : ℝ) (hd : 0<delta) : SchwartzMap ℝ ℂ :=
  dilatedSlopeWindow slopePartition delta⁻¹ (inv_ne_zero hd.ne')

theorem scaledSlopePartition_apply (delta : ℝ) (hd : 0<delta) (x : ℝ) :
    scaledSlopePartition delta hd x=slopePartition (x/delta) := by
  rw [scaledSlopePartition,dilatedSlopeWindow_apply]
  congr 1
  ring

theorem scaledSlopePartition_support (delta : ℝ) (hd : 0<delta) (x : ℝ)
    (hx : scaledSlopePartition delta hd x≠0) : |x|≤delta := by
  rw [scaledSlopePartition_apply] at hx
  have h := slopePartition_support _ hx
  rw [abs_div,abs_of_pos hd] at h
  exact (div_le_one hd).mp h

theorem finiteSlopePartition_sum (K : ℕ) (delta d s : ℝ) (hdelta : 0<delta) (hd : 0<d)
    (hcover : |s/(delta*d)|≤K) :
    ∑ n∈finiteSlopeLabels K,
      scaledSlopePartition delta hdelta ((s-finiteSlopeCenter K delta d n)/d)=1 := by
  have heq (n : ℕ) : scaledSlopePartition delta hdelta ((s-finiteSlopeCenter K delta d n)/d)=
      slopePartition (s/(delta*d)+K-(n:ℝ)) := by
    rw [scaledSlopePartition_apply]
    congr 1
    unfold finiteSlopeCenter
    field_simp
    ring
  simp_rw [heq]
  exact slopePartition_sum_one K (s/(delta*d)) hcover

theorem exists_finiteSlopeCenter_multiplicity (delta H : ℝ) (hdelta : 0<delta) (hH : 0≤H) :
    ∃ M : ℕ, ∀ (K : ℕ) (d : ℝ), 0<d →
      SourceSlopeLabels.LocalMultiplicity (Finset.univ : Finset (finiteSlopeLabels K))
        (fun n => finiteSlopeCenter K delta d n.val) (H*d) M := by
  obtain ⟨J,hJ⟩ := exists_nat_gt (H/(2*delta))
  refine ⟨2*J+1,?_⟩
  intro K d hd
  have hJ' := (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hdelta)).mp hJ
  have hh : H*d≤2*J*(delta*d) := by nlinarith
  have hi : Function.Injective (fun n : finiteSlopeLabels K => (n.val:ℤ)) := by
    intro x y h
    change (x.val:ℤ)=(y.val:ℤ) at h
    exact Subtype.ext (Int.ofNat.inj h)
  have h := SourceSlopeLabels.injective_integer_multiplicity
    (fun n : finiteSlopeLabels K => (n.val:ℤ)) hi (-delta*d*K) (delta*d) (H*d)
    (mul_pos hdelta hd) (mul_nonneg hH hd.le) J hh
  convert h using 1
  ext n
  simp only [finiteSlopeCenter,Int.cast_natCast]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
